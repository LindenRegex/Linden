/** Type definitions. */

interface GroupState {
  id: number;
  startIdx: number; // inclusive
  endIdx: number | null; // exclusive; null while the group is open
}

interface EngineState {
  idx: number;
  dir: "Forward" | "Backward";
  groups: GroupState[];
}

interface TreeNode {
  name: string;
  arg: string;
  result: "Match" | "Mismatch" | null;
  hasGhostSubtree: boolean;
  regexId: number | null;
  pre: EngineState | null;
  post: EngineState | null;
  children: TreeNode[];
}

// [first:last]: inclusive on both sides
type HoverFn = (first: number | null, last: number | null, event?: Event) => void;

/** A JavaScript regex's flags, keyed by their long names. */
interface RegexFlags {
  hasIndices: boolean;
  global: boolean;
  ignoreCase: boolean;
  multiline: boolean;
  dotAll: boolean;
  unicode: boolean;
  unicodeSets: boolean;
  sticky: boolean;
}

/** The result of a Linden run (as encoded by Melange). */
type RunResult =
  | { NAME: "Ok"; VAL: TreeNode }
  | { NAME: "Error"; VAL: string };
