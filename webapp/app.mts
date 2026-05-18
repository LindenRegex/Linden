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
  constructor(private readonly fn: () => void, private readonly delay: number) {}

  schedule(): void {
    clearTimeout(this.timer);
    this.timer = setTimeout(this.fn, this.delay);
  }
}

/// Input console

class RegexConsole {
  readonly regexInput = byId<HTMLTextAreaElement>("regex");
  readonly stringInput = byId<HTMLTextAreaElement>("string");
  readonly lastIndexInput = byId<HTMLInputElement>("last-index");
  readonly regexView = byId("regex-view");

  private readonly error = byId("regex-error");
  private readonly exec = byId("exec-result");

  constructor() {}

  static fitAreaToContent(box: HTMLTextAreaElement): void {
    box.cols = Math.max(1, box.value.length);
    box.style.height = "auto";
    box.style.height = `${box.scrollHeight}px`;
  }

  static fitInputToContent(box: HTMLInputElement): void {
    box.style.width = `${2 + Math.max(1, box.value.length)}ch`;
  }

  fitInputs(): void {
    RegexConsole.fitAreaToContent(this.regexInput);
    RegexConsole.fitAreaToContent(this.stringInput);
    RegexConsole.fitInputToContent(this.lastIndexInput);
    this.lastIndexInput.max = String(1 + this.stringInput.value.length);
  }

  /** Compute and format the result of a regex.exec at `lastIndex`. */
  static execResult(pattern: string, s: string, lastIndex: number): string | null {
    try {
      const r = new RegExp(pattern, "y");
      r.lastIndex = lastIndex;
      const m = r.exec(s);
      return m ? `${JSON.stringify([...m])}  (index ${m.index})` : "null";
    } catch {
      return null;
    }
  }

  /** Display or clear a parsing error. */
  renderError(error: string | null): void {
    this.regexInput.classList.toggle("bad", error !== null);
    this.error.textContent = error ?? "";
  }

  /** Display the results of the browser's own `exec`. */
  renderExec(success: boolean) {
    this.exec.textContent = !success ? "" :
      RegexConsole.execResult(this.regexInput.value, this.stringInput.value, +this.lastIndexInput.value) ?? "";
  }
}

/// Regex tree pane

class TreeView {
  private readonly root = byId("tree");
  private last: TreeNode | null = null;
  // re-fits the current SVG to its container, without rebuilding the tree
  private refit: (() => void) | undefined;
  private readonly refitSoon = new Debounced(() => this.refit?.(), 150);

  constructor(private readonly onHover: (d: LaidOutNode | null) => void) {
    window.addEventListener("resize", () => this.refitSoon.schedule());
  }

  /** Draw a tree. */
  draw(tree?: TreeNode | null): void {
    if (tree !== undefined) this.last = tree;
    if (this.last) this.refit = render(this.last, this.root, this.onHover);
    else { this.root.replaceChildren(); this.refit = undefined; }
  }

  /** Show an out-of-fuel notice with a retry button. */
  showRetry(fuel: number, onRetry: () => void): void {
    this.last = null;
    this.refit = undefined;
    const link = el("a", "retry", `try harder (${fuel})`);
    link.addEventListener("click", onRetry);
    this.root.replaceChildren(el("div", "tree-msg", "Stack overflow; ", link));
  }
}

/// Engine-state pane

class StatePane {
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
  show(d: LaidOutNode, input: string): void {
    this.root.replaceChildren();
    const state = d.data.post ?? d.data.pre;
    if (!state) return;

    const chars = [...input];

    const fmtRange = (lo: number, hi: number | null): string =>
      `[${lo}:${hi ?? ""})`;

    const arrow = { Backward: "←", Forward: "→" }[state.dir];
    this.root.append(StatePane.row(`${arrow}`, input, state.idx, state.idx, "caret", fmtRange(0, state.idx)));

    for (const g of state.groups) {
      const endIdx = g.endIdx ?? state.idx;
      this.root.append(StatePane.row(`$${g.id}`, input, g.startIdx, endIdx, "highlighted-span", fmtRange(g.startIdx, g.endIdx)));
    }
  }
}

/// Main app

class App {
  private fuel = 30;
  private readonly console = new RegexConsole();
  private readonly tree = new TreeView((d) => this.onHover(d));
  private readonly state = new StatePane();
  private readonly recomputeSoon = new Debounced(() => this.recompute(), 120);

  constructor() {
    this.console.regexInput.addEventListener("input", () => this.scheduleRecompute());
    this.console.stringInput.addEventListener("input", () => this.scheduleRecompute());
    this.console.lastIndexInput.addEventListener("input", () => this.scheduleRecompute());
    this.console.regexView.addEventListener("mouseleave", () => this.onHover(null));
  }

  /** Start with a sample regex. */
  start(): void {
    this.console.regexInput.value = "(?:a|(?:a(b)|a))bc";
    this.console.stringInput.value = "abc";
    this.console.lastIndexInput.value = "0";
    this.scheduleRecompute();
  }

  /** Resize the inputs now, and recompute once typing pauses. */
  private scheduleRecompute(): void {
    this.console.fitInputs();
    this.recomputeSoon.schedule();
  }

  /** Recompute the tree */
  private recompute(): void {
    this.state.clear();
    this.console.renderError(null);

    const r = this.console.regexInput.value;
    const s = this.console.stringInput.value;
    const lastIndex = +this.console.lastIndexInput.value;
    const hl: HoverFn = (first, last, e) =>
      this.highlight(first !== null && last !== null ? { first, last } : null, e);
    const result = run(r, s, lastIndex, this.fuel, this.console.regexView, hl);

    if (result.NAME === "Ok") {
      this.tree.draw(result.VAL);
      this.console.renderError(null);
      this.console.renderExec(true);
    } else {
      this.console.renderExec(false);
      if (result.NAME === "Error" && result.VAL === "out of fuel") {
        this.fuel = Math.round(this.fuel * 1.2);
        this.tree.showRetry(this.fuel, () => this.recompute());
      } else {
        this.console.renderError(result.VAL);
        this.tree.draw(null);
      }
    }
  }

  /** Highlight subregexes matching a hovered node. */
  private onHover(d: LaidOutNode | null): void {
    if (d) this.state.show(d, this.console.stringInput.value);
    else this.state.clear();
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
