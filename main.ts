// mend: one patch tool for every AI edit format. Reads unified diffs,
// SEARCH/REPLACE blocks, V4A patches and JSON tool calls to the written
// specification in SPEC.md, finds the lines an edit names even when the
// model drifted their whitespace or indentation, and changes every file
// or none. Node 22, standard library only.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and this file hands over to runner.ts (the last lines below): keep that
// hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') &&
    p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// ---- Files as lines -------------------------------------------------------
// A file is its lines plus the break that joins them and whether it ends
// with one. The break is CRLF when the file's first line feed follows a
// carriage return, and LF otherwise.
interface FileState {
  lines: string[];
  br: string;
  ends: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', ends: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const ends = text.endsWith(br);
  if (ends) parts.pop();
  return { lines: parts, br, ends };
}

function serializeFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.ends ? f.br : '');
}

function fileState(text: string | null): FileState | null {
  return text === null ? null : parseFile(text);
}

// ---- Three-tier matching --------------------------------------------------
// Tier 0: every line equal. Tier 1: equal once trailing spaces and tabs are
// removed from both. Tier 2: equal once leading and trailing spaces and
// tabs are removed from both.
function norm(line: string, tier: number): string {
  if (tier === 0) return line;
  if (tier === 1) return line.replace(/[ \t]+$/, '');
  return line.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

function occurrences(lines: string[], pat: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  if (pat.length === 0 || pat.length > lines.length) return out;
  const np = pat.map((l) => norm(l, tier));
  for (let i = from; i + pat.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < pat.length; j++) {
      if (norm(lines[i + j]!, tier) !== np[j]) { ok = false; break; }
    }
    if (ok) out.push(i);
  }
  return out;
}

// The first tier at which the pattern occurs at least once, and where.
function findTier(lines: string[], pat: string[], strict: boolean, from = 0): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const positions = occurrences(lines, pat, tier, from);
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

const leadingWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};

// One side of an edit: old lines O and new lines N. `newContextAt`
// maps each new line to the index of the old line it is the context
// twin of, or null when the line is new text of its own. Context lines
// keep their order in both sides, but deletions and insertions shift
// their positions, so the mapping is by context order, not by index.
interface EditSide {
  oldLines: string[];
  newLines: string[];
  newContextAt: Array<number | null>;
}

// Replace the matched lines at `pos` with the new lines, applying the
// tier-2 re-indentation rule to the new lines that are not context lines.
function spliceSide(f: FileState, side: EditSide, pos: number, tier: number): void {
  const matched = f.lines.slice(pos, pos + side.oldLines.length);
  const out: string[] = [];
  if (tier === 2 && side.oldLines.length > 0) {
    const pfx = leadingWs(side.oldLines[0]!);
    const ffx = leadingWs(f.lines[pos]!);
    for (let i = 0; i < side.newLines.length; i++) {
      const ctx = side.newContextAt[i];
      if (ctx !== null && ctx !== undefined) { out.push(matched[ctx]!); continue; }
      const line = side.newLines[i]!;
      if (line !== '' && line.trim() !== '' && line.startsWith(pfx)) out.push(ffx + line.slice(pfx.length));
      else out.push(line);
    }
  } else {
    for (let i = 0; i < side.newLines.length; i++) {
      const ctx = side.newContextAt[i];
      out.push(ctx !== null && ctx !== undefined ? matched[ctx]! : side.newLines[i]!);
    }
  }
  f.lines.splice(pos, side.oldLines.length, ...out);
}

// ---- The tree -------------------------------------------------------------
// The tree as the edits leave it: changed paths in `now` (null: deleted),
// the rest read from disk.
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- JSON edits (SPEC.md section 9) ---------------------------------------
// One JSON edit object, or null when it is not one.
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' &&
    (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) &&
    typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const f = parseFile(before);
      if (line < 0 || line > f.lines.length) throw new Fail('no-match', p);
      f.lines.splice(line, 0, ...add);
      tree.now.set(p, serializeFile(f));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- Unified diffs (SPEC.md section 6) ------------------------------------
// A hunk body line: context, old, new, or a backslash marker.
type BodyItem = { kind: 'ctx' | 'old' | 'new' | 'mark'; text: string };

interface Hunk {
  a: number;
  body: BodyItem[];
}

// The path after `--- ` or `+++ `: text after the four characters, up to
// the first tab, surrounding spaces removed, a leading a/ or b/ removed.
// `/dev/null` is returned as null.
function diffPath(line: string): string | null {
  let p = line.slice(4).split('\t')[0]!.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

function hunkSide(h: Hunk): EditSide {
  const oldLines: string[] = [];
  const newLines: string[] = [];
  const newContextAt: Array<number | null> = [];
  let oIdx = 0;
  for (const it of h.body) {
    if (it.kind === 'ctx') { oldLines.push(it.text); newLines.push(it.text); newContextAt.push(oIdx); oIdx += 1; }
    else if (it.kind === 'old') { oldLines.push(it.text); oIdx += 1; }
    else if (it.kind === 'new') { newLines.push(it.text); newContextAt.push(null); }
  }
  return { oldLines, newLines, newContextAt };
}

// Whether a `\` line follows the hunk's last context or `+` line: the
// file then ends without a line break.
function hunkNoBreak(h: Hunk): boolean {
  let last = -1;
  h.body.forEach((it, i) => { if (it.kind === 'ctx' || it.kind === 'new') last = i; });
  if (last < 0) return false;
  return h.body[last + 1]?.kind === 'mark';
}

interface Section {
  oldPath: string | null;
  newPath: string | null;
  creation: boolean;
  deletion: boolean;
  hunks: Hunk[];
}

function parseUnified(lines: string[], strict: boolean, moves: Array<[string, string]>): Edit[] {
  const sections: Section[] = [];
  let cur: {
    oldPath: string | null; newPath: string | null; hasPair: boolean;
    renameFrom: string | null; renameTo: string | null;
    diffOld: string | null; diffNew: string | null;
    creation: boolean; deletion: boolean; hunks: Hunk[];
  } | null = null;

  const close = (): void => {
    if (cur === null) return;
    let oldPath = cur.hasPair ? cur.oldPath : cur.renameFrom ?? cur.diffOld;
    let newPath = cur.hasPair ? cur.newPath : cur.renameTo ?? cur.diffNew;
    if (cur.creation) oldPath = null;
    if (cur.deletion) newPath = null;
    sections.push({ oldPath, newPath, creation: cur.creation, deletion: cur.deletion, hunks: cur.hunks });
    cur = null;
  };

  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      close();
      cur = {
        oldPath: null, newPath: null, hasPair: false,
        renameFrom: null, renameTo: null,
        diffOld: m[1]!, diffNew: m[2]!,
        creation: false, deletion: false, hunks: [],
      };
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur !== null && cur.hunks.length === 0 && !cur.hasPair) {
        // The pair of the section whose header is still open.
        cur.oldPath = diffPath(line);
        cur.newPath = diffPath(lines[i + 1]!);
        cur.hasPair = true;
        i += 2;
        continue;
      }
      close();
      cur = {
        oldPath: diffPath(line), newPath: diffPath(lines[i + 1]!), hasPair: true,
        renameFrom: null, renameTo: null,
        diffOld: null, diffNew: null,
        creation: false, deletion: false, hunks: [],
      };
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: Number(m[1]), body: [] };
      i += 1;
      // The body runs until the first line that is not a body line, a
      // `diff --git` line, a `--- ` line followed by `+++ `, or the end.
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b.startsWith('@@')) break;
        if (b === '') { hunk.body.push({ kind: 'ctx', text: '' }); i += 1; continue; }
        const c = b[0];
        if (c === ' ') { hunk.body.push({ kind: 'ctx', text: b.slice(1) }); i += 1; continue; }
        if (c === '-') { hunk.body.push({ kind: 'old', text: b.slice(1) }); i += 1; continue; }
        if (c === '+') { hunk.body.push({ kind: 'new', text: b.slice(1) }); i += 1; continue; }
        if (c === '\\') { hunk.body.push({ kind: 'mark', text: b }); i += 1; continue; }
        break;
      }
      // Empty lines at the end of a body are not part of it.
      while (hunk.body.length > 0 && hunk.body[hunk.body.length - 1]!.kind === 'ctx' &&
        hunk.body[hunk.body.length - 1]!.text === '') hunk.body.pop();
      cur.hunks.push(hunk);
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      // Inside a section's header.
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) cur.creation = true;
      else if (line.startsWith('deleted file mode')) cur.deletion = true;
      i += 1;
      continue;
    }
    // Prose and anything outside a body: ignored.
    i += 1;
  }
  close();

  const edits: Edit[] = [];
  for (const s of sections) {
    edits.push(unifiedEdit(s, strict, moves));
  }
  return edits;
}

function unifiedEdit(s: Section, strict: boolean, moves: Array<[string, string]>): Edit {
  return (tree) => {
    const isCreation = s.creation || (s.oldPath === null && s.newPath !== null);
    const isDeletion = s.deletion || (s.newPath === null && s.oldPath !== null);
    if (s.oldPath === null && s.newPath === null && !s.creation && !s.deletion) return;
    const isMove = !isCreation && !isDeletion && s.oldPath !== null && s.newPath !== null && s.oldPath !== s.newPath;
    const target = isCreation ? s.newPath! : s.oldPath!;

    // Every path the edit names is checked for safety before anything else.
    if (s.oldPath !== null && !safe(s.oldPath)) throw new Fail('unsafe', s.oldPath);
    if (s.newPath !== null && !safe(s.newPath)) throw new Fail('unsafe', s.newPath);

    if (isCreation) {
      if (tree.get(target) !== null) throw new Fail('exists', target);
      const outLines: string[] = [];
      let noBreak = false;
      for (const h of s.hunks) {
        let lastNew = -1;
        h.body.forEach((it, idx) => {
          if (it.kind === 'new') { outLines.push(it.text); lastNew = idx; }
        });
        // SPEC.md section 6: a created file ends with a line break unless
        // a `\` line follows its LAST `+` line. A mark after an earlier
        // hunk must not drop the final break, so only the hunk holding
        // the file's last `+` line decides, and only a mark right
        // after that line counts; later hunks with `+` lines override.
        if (lastNew >= 0) noBreak = h.body[lastNew + 1]?.kind === 'mark';
      }
      const f: FileState = { lines: outLines, br: '\n', ends: outLines.length > 0 && !noBreak };
      tree.now.set(target, serializeFile(f));
      return;
    }
    if (isDeletion) {
      if (tree.get(target) === null) throw new Fail('missing', target);
      tree.now.set(target, null);
      return;
    }
    if (tree.get(target) === null) throw new Fail('missing', target);
    if (isMove && tree.get(s.newPath!) !== null) throw new Fail('exists', s.newPath!);

    const f = parseFile(tree.get(target)!);
    let d = 0;
    for (const h of s.hunks) {
      const side = hunkSide(h);
      if (side.oldLines.length === 0) {
        const at = Math.min(h.a + d, f.lines.length);
        const wasEnd = at >= f.lines.length;
        f.lines.splice(at, 0, ...side.newLines);
        if (wasEnd) f.ends = !hunkNoBreak(h);
        d += side.newLines.length;
        continue;
      }
      const found = findTier(f.lines, side.oldLines, strict);
      if (found === null) throw new Fail('no-match', target);
      const want = h.a - 1 + d;
      let best = found.positions[0]!;
      for (const pos of found.positions) {
        if (Math.abs(pos - want) < Math.abs(best - want)) best = pos;
      }
      const touchesEnd = best + side.oldLines.length >= f.lines.length;
      spliceSide(f, side, best, found.tier);
      if (touchesEnd) f.ends = !hunkNoBreak(h);
      d += side.newLines.length - side.oldLines.length;
    }
    const text = serializeFile(f);
    if (isMove) {
      tree.now.set(s.newPath!, text);
      tree.now.set(target, null);
      moves.push([target, s.newPath!]);
    } else {
      tree.now.set(target, text);
    }
  };
}

// ---- SEARCH/REPLACE blocks (SPEC.md section 7) ---------------------------
function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') { i += 1; continue; }
    const searchLine = i;
    // The path is the nearest line before the SEARCH line, after the
    // previous block's REPLACE line, that is not blank and does not
    // start with three backticks.
    let path: string | null = null;
    for (let j = searchLine - 1; j > prevEnd; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    // The ======= line, then the >>>>>>> REPLACE line.
    let sep = -1;
    let end = -1;
    for (let j = searchLine + 1; j < lines.length; j++) {
      const t = lines[j]!.trimEnd();
      if (sep < 0 && t === '=======') { sep = j; continue; }
      if (sep >= 0 && t === '>>>>>>> REPLACE') { end = j; break; }
    }
    if (sep < 0 || end < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, sep);
    const newLines = lines.slice(sep + 1, end);
    const p = path;
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const f: FileState = { lines: [...newLines], br: '\n', ends: true };
        tree.now.set(p, serializeFile(f));
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const f = parseFile(before);
      const found = findTier(f.lines, oldLines, strict);
      if (found === null) throw new Fail('no-match', p);
      if (found.positions.length > 1) throw new Fail('ambiguous', p);
      const side: EditSide = { oldLines, newLines, newContextAt: newLines.map(() => null) };
      spliceSide(f, side, found.positions[0]!, found.tier);
      tree.now.set(p, serializeFile(f));
    });
    prevPath = p;
    prevEnd = end;
    i = end + 1;
  }
  return edits;
}

// ---- V4A patches (SPEC.md section 8) --------------------------------------
type V4aSection =
  | { kind: 'add'; path: string; lines: string[] }
  | { kind: 'delete'; path: string }
  | { kind: 'update'; path: string; moveTo: string | null; chunks: V4aChunk[] };

interface V4aChunk {
  anchor: string | null;
  endOfFile: boolean;
  side: EditSide;
}

function parseV4a(lines: string[], strict: boolean, moves: Array<[string, string]>): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last -= 1;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);

  const sections: V4aSection[] = [];
  let i = first + 1;
  const headerOf = (l: string): { kind: 'add' | 'delete' | 'update'; path: string } | null => {
    const t = l.trim();
    if (t.startsWith('*** Add File: ')) return { kind: 'add', path: t.slice('*** Add File: '.length).trim() };
    if (t.startsWith('*** Delete File: ')) return { kind: 'delete', path: t.slice('*** Delete File: '.length).trim() };
    if (t.startsWith('*** Update File: ')) return { kind: 'update', path: t.slice('*** Update File: '.length).trim() };
    return null;
  };

  while (i < last) {
    if (blank(lines[i]!)) { i += 1; continue; }
    const head = headerOf(lines[i]!);
    if (head === null) throw new Exit2(`error: parse ${i + 1}`);
    const headLine = i;
    i += 1;
    if (head.kind === 'delete') {
      // A Delete File section has no lines.
      sections.push({ kind: 'delete', path: head.path });
      continue;
    }
    // Collect the section's lines until the next section header or End Patch.
    const body: string[] = [];
    const bodyLines: number[] = [];
    while (i < last) {
      if (headerOf(lines[i]!) !== null) break;
      body.push(lines[i]!);
      bodyLines.push(i);
      i += 1;
    }
    // Blank lines at the end of a section are not part of it: a line
    // that is empty or only whitespace counts as blank here.
    while (body.length > 0 && blank(body[body.length - 1]!)) { body.pop(); bodyLines.pop(); }
    if (head.kind === 'add') {
      const out: string[] = [];
      for (let k = 0; k < body.length; k++) {
        const l = body[k]!;
        if (l === '') out.push('');
        else if (l.startsWith('+')) out.push(l.slice(1));
        else throw new Exit2(`error: parse ${bodyLines[k]! + 1}`);
      }
      sections.push({ kind: 'add', path: head.path, lines: out });
      continue;
    }
    // Update File: optional `*** Move to:` first, then chunks.
    let moveTo: string | null = null;
    let start = 0;
    if (body.length > 0 && body[0]!.trim().startsWith('*** Move to: ')) {
      moveTo = body[0]!.trim().slice('*** Move to: '.length).trim();
      start = 1;
    }
    const chunks: V4aChunk[] = [];
    let k = start;
    while (k < body.length) {
      let anchor: string | null = null;
      let endOfFile = false;
      const t = body[k]!.trim();
      if (t.startsWith('@@')) {
        anchor = t.slice(2).trim();
        if (anchor === '') anchor = null;
        k += 1;
      }
      const oldLines: string[] = [];
      const newLines: string[] = [];
      const newContextAt: Array<number | null> = [];
      let sawBody = false;
      let oIdx = 0;
      while (k < body.length) {
        const l = body[k]!;
        const lt = l.trim();
        if (lt === '*** End of File') { endOfFile = true; k += 1; break; }
        if (lt.startsWith('@@')) break;
        if (l === '') { oldLines.push(''); newLines.push(''); newContextAt.push(oIdx); oIdx += 1; sawBody = true; k += 1; continue; }
        const c = l[0];
        if (c === ' ') { oldLines.push(l.slice(1)); newLines.push(l.slice(1)); newContextAt.push(oIdx); oIdx += 1; sawBody = true; k += 1; continue; }
        if (c === '-') { oldLines.push(l.slice(1)); oIdx += 1; sawBody = true; k += 1; continue; }
        if (c === '+') { newLines.push(l.slice(1)); newContextAt.push(null); sawBody = true; k += 1; continue; }
        throw new Exit2(`error: parse ${bodyLines[k]! + 1}`);
      }
      // A chunk with no body lines is an empty edit at the cursor.
      chunks.push({ anchor, endOfFile, side: { oldLines, newLines, newContextAt } });
      if (endOfFile) break;
      // A chunk ends at the next @@ line; loop again for it.
      if (k < body.length && !body[k]!.trim().startsWith('@@')) {
        // The body loop stopped only at @@, End of File or the end, so
        // anything else here is unreachable; guard anyway.
        throw new Exit2(`error: parse ${bodyLines[k]! + 1}`);
      }
    }
    if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${headLine + 1}`);
    sections.push({ kind: 'update', path: head.path, moveTo, chunks });
  }

  const edits: Edit[] = [];
  for (const s of sections) {
    if (s.kind === 'add') {
      const p = s.path;
      const fileLines = s.lines;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const f: FileState = { lines: [...fileLines], br: '\n', ends: true };
        tree.now.set(p, serializeFile(f));
      });
    } else if (s.kind === 'delete') {
      const p = s.path;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      const p = s.path;
      const moveTo = s.moveTo;
      const chunks = s.chunks;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
        const f = parseFile(before);
        let cursor = 0;
        for (const chunk of chunks) {
          if (chunk.anchor !== null) {
            const found = findTier(f.lines, [chunk.anchor], strict, cursor);
            if (found === null) throw new Fail('no-match', p);
            cursor = found.positions[0]! + 1;
          }
          const side = chunk.side;
          if (side.oldLines.length === 0) {
            const at = chunk.endOfFile ? f.lines.length : cursor;
            f.lines.splice(at, 0, ...side.newLines);
            cursor = at + side.newLines.length;
            continue;
          }
          const found = findTier(f.lines, side.oldLines, strict, cursor);
          if (found === null) throw new Fail('no-match', p);
          let pos: number | null = null;
          for (const cand of found.positions) {
            if (chunk.endOfFile && cand + side.oldLines.length !== f.lines.length) continue;
            pos = cand;
            break;
          }
          if (pos === null) throw new Fail('no-match', p);
          spliceSide(f, side, pos, found.tier);
          cursor = pos + side.newLines.length;
        }
        const text = serializeFile(f);
        if (moveTo !== null) {
          tree.now.set(moveTo, text);
          tree.now.set(p, null);
          moves.push([p, moveTo]);
        } else {
          tree.now.set(p, text);
        }
      });
    }
  }
  return edits;
}

// ---- Invocation, output and atomicity (SPEC.md sections 1, 2 and 10) -----
function byteOrder(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const moves: Array<[string, string]> = [];
  let edits: Edit[];
  try {
    edits = kind === 'json' ? jsonEdits(text, lines)
      : kind === 'unified' ? parseUnified(lines, strict, moves)
      : kind === 'search-replace' ? parseSearchReplace(lines, strict)
      : parseV4a(lines, strict, moves);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const mvLen = moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      moves.length = mvLen;
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  }
  // Changed paths, in byte order; a successful move replaces its D and A
  // pair with one R line, sorted by the new path.
  interface Row { key: string; text: string; }
  const rows: Row[] = [];
  const changed = new Map<string, string | null>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was !== now) changed.set(p, now);
  }
  for (const [p, now] of changed) {
    rows.push({ key: p, text: `${now === null ? 'D' : tree.original(p) === null ? 'A' : 'M'} ${p}` });
  }
  for (const [oldP, newP] of moves) {
    const di = rows.findIndex((r) => r.text === `D ${oldP}`);
    const ai = rows.findIndex((r) => r.text === `A ${newP}`);
    if (di >= 0 && ai >= 0 && tree.original(oldP) !== null && tree.original(newP) === null) {
      rows.splice(Math.max(di, ai), 1);
      rows.splice(Math.min(di, ai), 1);
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
    }
  }
  rows.sort((a, b) => byteOrder(a.key, b.key));
  if (!check) {
    for (const [p, now] of changed) {
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
