/** TypeScript interface for the entry point exported by Main.ml. */

/** Parse `pattern` with `flags` and run it on `input` from `startIdx` with `fuel`.
    The parsed regex is displayed in `regexView` with `onHover` handlers.  */
export function run(
  pattern: string,
  flags: RegexFlags,
  input: string,
  startIdx: number,
  fuel: number,
  regexView: HTMLElement,
  onHover: HoverFn,
): RunResult;
