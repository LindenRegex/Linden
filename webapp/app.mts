/** Linden regex explorer */

import { run } from "./Main.mjs";
import { render } from "./tree-render.mjs";
import type { LaidOutNode } from "./tree-render.mjs";

/// Utilities

/** Like `getElementById`, but with types */
function byId<E extends HTMLElement = HTMLElement>(id: string): E {
  return document.getElementById(id) as E;
}

/** Build an element */
function el(tag: string, cls: string | null, ...children: (string | Node)[]): HTMLElement {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  for (const c of children) e.append(c);
  return e;
}

/** Runs `fn` once calls to schedule() have paused for `delay` ms. */
class Debounced {
  private timer: ReturnType<typeof setTimeout> | undefined;
  constructor(public fn: (() => void) | undefined, private readonly delay: number) {}

  schedule(): void {
    clearTimeout(this.timer);
    if (this.fn) this.timer = setTimeout(this.fn, this.delay);
  }

  /** Run `fn` now, cancelling any pending call. */
  force(): void {
    clearTimeout(this.timer);
    this.fn?.();
  }
}

/// Input console

interface ConsoleState {
  pattern: string;
  input: string;
  flags: RegexFlags;
  flagString: string;
  startIndex: number;
}

class RegexConsole {
  private readonly stringInput = byId<HTMLTextAreaElement>("string");
  private readonly rawCheckbox = byId<HTMLInputElement>("raw");
  private readonly stringErrorMessage = byId("string-error");

  private readonly regexInput = byId<HTMLTextAreaElement>("regex");
  private readonly regexFlags = [...byId("regex-flags").querySelectorAll<HTMLInputElement>("input")];
  private readonly regexErrorMessage = byId("regex-error");

  private readonly stickyPrefixText = byId("sticky-prefix");
  private readonly lastIndexInput = byId<HTMLInputElement>("last-index");
  private readonly exec = byId("exec-result");

  readonly regexView = byId("regex-view");

  // Browsers don't like constant history updates
  private readonly urlWriter = new Debounced(() => this.writeToUrlHash(), 500);

  constructor(private readonly onStateChanged: () => void) {
    const sync = () => { this.urlWriter.schedule(); this.syncUI(); };
    this.regexInput.addEventListener("input", sync);
    this.stringInput.addEventListener("input", sync);
    this.lastIndexInput.addEventListener("input", sync);
    this.rawCheckbox.addEventListener("change", sync);
    this.regexFlags.forEach((box) => box.addEventListener("change", sync));
  }

  static fitAreaToContent(box: HTMLTextAreaElement): void {
    box.cols = Math.max(1, box.value.length);
    box.style.height = "auto";
    box.style.height = `${box.scrollHeight}px`;
  }

  static fitInputToContent(box: HTMLInputElement): void {
    box.style.width = `${2 + Math.max(1, box.value.length)}ch`;
  }

  /** The current input string, possibly parsed as a JSON string */
  private input(): string | null {
    try {
      const value = this.stringInput.value;
      return this.rawCheckbox.checked ? value : JSON.parse(`"${value}"`);
    } catch (e) {
      this.renderStringError(String(e));
      return null;
    }
  }

  /** Read checked flags as their string representation, e.g. "dy". */
  private flagString(): string {
    return this.regexFlags.filter((box) => box.checked)
      .map((box) => box.dataset.str).join("");
  }

  /** Snapshot the inputs (input-string decoding may throw). */
  state(): ConsoleState | null {
    const input: string | null = this.input();
    if (input == null) return null;
    return {
      input,
      pattern: this.regexInput.value,
      flags: Object.fromEntries(
        this.regexFlags.map((box) => [box.id.replace("flag-", ""), box.checked] as const),
      ) as unknown as RegexFlags,
      flagString: this.flagString(),
      startIndex: +this.lastIndexInput.value,
    };
  }

  /** Read inputs from the `#…` part of the URL, if any. */
  readFromUrlHash(): void {
    const q = new URLSearchParams(location.hash.slice(1));
    for (const input of [this.regexInput, this.stringInput, this.lastIndexInput])
      input.value = q.get(input.id) ?? input.value;
    for (const box of [this.rawCheckbox])
      box.checked = q.has(box.id) ? q.get(box.id) === "1" : box.checked;
    const flags = q.get("flags");
    if (flags !== null)
      for (const box of this.regexFlags)
        box.checked = flags.includes(box.dataset.str!);
  }

  /** Write inputs to `#…` part of the URL. */
  writeToUrlHash(): void {
    const q = new URLSearchParams();
    for (const input of [this.regexInput, this.stringInput, this.lastIndexInput])
      q.set(input.id, input.value);
    for (const box of [this.rawCheckbox])
      q.set(box.id, box.checked ? "1" : "0");
    q.set("flags", this.flagString());
    history.replaceState(null, "", `#${q}`);
  }

  /** Resize the inputs, toggle the sticky UI, and notify the app. */
  syncUI(): void {
    RegexConsole.fitAreaToContent(this.regexInput);
    RegexConsole.fitAreaToContent(this.stringInput);
    RegexConsole.fitInputToContent(this.lastIndexInput);
    this.lastIndexInput.max = String(1 + this.stringInput.value.length);
    this.stickyPrefixText.hidden = !byId<HTMLInputElement>("flag-sticky").checked;
    this.onStateChanged();
  }

  /** Compute and format the result of a regex.exec at `lastIndex`. */
  execResult(state: ConsoleState): string {
    try {
      const { pattern, input, flagString, startIndex } = state;
      const r = new RegExp(pattern, flagString);
      r.lastIndex = startIndex;
      const m = r.exec(input);
      return m ? `${JSON.stringify([...m])}  (index ${m.index})` : "null";
    } catch (e) {
      return String(e);
    }
  }

  /** Display or clear an error. */
  private renderError(error: string | null, source: Element, target: Element): void {
    source.classList.toggle("bad", error !== null);
    target.textContent = error ?? "";
  }

  renderStringError(error: string | null): void {
    this.renderError(error, this.stringInput, this.stringErrorMessage);
  }

  renderRegexError(error: string | null): void {
    this.renderError(error, this.regexInput, this.regexErrorMessage);
  }

  clearErrors(): void {
    this.renderStringError(null);
    this.renderRegexError(null);
  }

  /** Display the results of the browser's own `exec`. */
  renderExec(state: ConsoleState | null): void {
    this.exec.textContent = state ? this.execResult(state) : "";
  }
}

/// Regex tree pane

class TreeView {
  private readonly root = byId("tree");
  private readonly refitScheduler: Debounced = new Debounced(undefined, 120);

  constructor(private readonly onHover: (d: LaidOutNode | null) => void) {
    window.addEventListener("resize", () => this.refitScheduler.schedule());
  }

  /** Draw a tree. */
  draw(tree: TreeNode): void {
    this.refitScheduler.fn = render(tree, this.root, this.onHover);
  }

  /** Empty the pane. */
  clear(): void {
    this.root.replaceChildren();
    this.refitScheduler.fn = undefined;
  }

  /** Show an out-of-fuel notice with a retry button. */
  showRetry(fuel: number, onRetry: () => void): void {
    this.clear();
    const link = el("a", "retry", `try harder (${fuel})`);
    link.addEventListener("click", onRetry);
    this.root.replaceChildren(el("div", "tree-msg", "Stack overflow; ", link));
  }
}

/// Engine-state pane

class StateView {
  private readonly root = byId("state");

  private static row(label: string, input: string, lo: number, hi: number, kind: string, range: string): HTMLElement  {
    const seg = (from: number, to?: number): string =>
      input.slice(from, to);
    return el(
      "div", "st-row",
      el("span", "st-label", label),
      seg(0, lo),
      el("span", kind, seg(lo, hi)),
      seg(hi),
      el("span", "st-dim", `  ${range}`),
    );
  }

  /** Empty the pane. */
  clear(): void {
    this.root.replaceChildren();
  }

  /** Show the state corresponding to a given node. */
  show(d: LaidOutNode): void {
    this.clear();

    const state = d.data.post ?? d.data.pre;

    const fmtRange = (lo: number, hi: number | null): string =>
      `[${lo}:${hi ?? ""})`;

    const idx = state.idx, input = state.input;
    const arrow = { Backward: "←", Forward: "→" }[state.dir];
    this.root.append(StateView.row(`${arrow}`, input, idx, idx, "caret", fmtRange(0, idx)));

    for (const g of state.groups) {
      const endIdx = g.endIdx ?? idx;
      this.root.append(StateView.row(`$${g.id}`, input, g.startIdx, endIdx, "highlighted-span", fmtRange(g.startIdx, g.endIdx)));
    }
  }
}

/// Main app

class App {
  private fuel = 30;
  private readonly treeView = new TreeView((d) => this.onHover(d));
  private readonly stateView = new StateView();
  private readonly recomputeScheduler = new Debounced(() => this.recompute(), 120);
  private readonly console = new RegexConsole(() => this.recomputeScheduler.schedule());

  start(): void {
    byId("panes").addEventListener("mouseleave", () => this.onHover(null));
    this.console.readFromUrlHash();
    this.console.syncUI();
    this.recomputeScheduler.force();
  }

  /** Recompute the tree */
  private recompute(): void {
    this.treeView.clear();
    this.stateView.clear();
    this.console.clearErrors();

    const st: ConsoleState | null = this.console.state();
    if (st === null) {
      this.console.renderExec(null);
      return;
    }

    const { pattern, flags, input, startIndex } = st;
    const hl: HoverFn = (range, e) => this.highlight(range, e);
    const result = run(pattern, flags, input, startIndex, this.fuel, this.console.regexView, hl);

    const success = result.NAME === "Ok";
    this.console.renderExec(success ? st : null);

    if (success) {
      this.treeView.draw(result.VAL);
    } else if (result.NAME === "Error" && result.VAL === "out of fuel") {
      this.fuel = Math.round(this.fuel * 1.2);
      this.treeView.showRetry(this.fuel, () => this.recompute());
    } else {
      this.console.renderRegexError(result.VAL);
    }
  }

  /** Highlight subregexes matching a hovered node. */
  private onHover(d: LaidOutNode | null): void {
    if (d) this.stateView.show(d);
    else this.stateView.clear();
    const regexId = d && d.data.regexId != null ? +d.data.regexId : null;
    this.highlight(regexId !== null ? { first: regexId, last: regexId } : null);
  }

  /** Highlight all subregexes whose id is in [first:last]. */
  private highlight(range: { first: number; last: number } | null, event?: Event): void {
    event?.stopPropagation();
    const inRange = (id: string | undefined) =>
      range !== null && id != null && +id >= range.first && +id <= range.last;
    const selector = "#regex-view .rx, #tree svg .tnode, #tree svg .tedge";
    document.querySelectorAll<SVGElement | HTMLElement>(selector).forEach((g) =>
      g.classList.toggle("subregex", inRange(g.dataset.regexId)));
  }
}

new App().start();
