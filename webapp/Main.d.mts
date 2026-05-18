/** TypeScript interface for the entry point exported by Main.ml. */

/** Parse `pattern` and run it on `input` with fuel.
    The parsed regex is displayed in `regexView` with `onHover` handlers.  */
export function run(
  pattern: string,
  input: string,
  fuel: number,
  regexView: HTMLElement,
  onHover: HoverFn,
): RunResult;
