/** D3 renderer for backtracking trees */

import * as d3 from "d3";
import type { HierarchyPointLink, HierarchyPointNode } from "d3";

const NODE_HEIGHT = 24;
const PADDING = 14;
const CHAR_WIDTH = 8.5;
const DEPTH_GAP = 40; // distance between tree layers

const FALLBACK_W = 900;
const FALLBACK_H = 560;

const MIN_ZOOM = 0.1;
const MAX_ZOOM = 2.5;
const MAX_FIT_SCALE = 1.1;
const FIT_MARGIN = 0.95;

const DIAMOND_EW = 9; // east and west sides
const DIAMOND_NS = 7; // north and south sides

type Shape = "pill" | "diamond" | "ribbon" | "square" | "round";
const SHAPE: Record<string, Shape> = {
  Start: "pill", Match: "pill", Choice: "diamond",
  "Read ": "ribbon", "BackRef ": "ribbon",
  "Open ": "square", "Close ": "square", "Reset ": "square",
};

interface Label {
  name: string;
  arg: string;
  mark: string;
}

export type LaidOutNode = HierarchyPointNode<TreeNode> & {
  label: Label;
  shape: Shape;
  width: number;
};

/** A node's actual width, including padding. */
const shapeWidth = (shape: Shape, len: number): number => {
  const width = Math.max(NODE_HEIGHT * 1.5, len * CHAR_WIDTH + PADDING);
  return width + (shape === "ribbon" ? PADDING : 0);
};

/** Draw a single node `d` into `target`. */
function drawShape(target: SVGGElement, d: LaidOutNode): void {
  const g = d3.select(target);

  const { shape, width: w } = d;
  const h = NODE_HEIGHT;

  const points = (ps: number[][]): string =>
    ps.map((p) => p.join(",")).join(" ");

  const diamond = () =>
    [[0, -h / 2 - DIAMOND_NS], [w / 2 + DIAMOND_EW, 0],
      [0, h / 2 + DIAMOND_NS], [-w / 2 - DIAMOND_EW, 0]];
  const ribbon = (notch: number) =>
    [[-w / 2, -h / 2], [w / 2 - notch, -h / 2], [w / 2, 0],
      [w / 2 - notch, h / 2], [-w / 2, h / 2], [-w / 2 + notch, 0]];

  if (shape === "diamond") {
    g.append("polygon").attr("points", points(diamond()));
  } else if (shape === "ribbon") {
    const ltr = ribbon(PADDING / 2);
    const pts = d.data.pre?.dir === "Backward" ? ltr.map(([x, y]) => [-x, y]) : ltr;
    g.append("polygon").attr("points", points(pts));
  } else {
    g.append("rect").attr("x", -w / 2).attr("y", -h / 2)
      .attr("width", w).attr("height", h)
      .attr("rx", { "pill": h / 2, "square": 0, "round": PADDING / 2 }[shape]);
  }
}

export type TreeHoverFn = (g: SVGGElement | null) => void;
export type TreeClickFn = (g: SVGGElement) => void;

export function render(data: TreeNode, container: HTMLElement, onHover: TreeHoverFn, onClick: TreeClickFn): () => void {
  const start: TreeNode = {
    name: "Start", arg: "", result: null, hasGhostSubtree: false,
    regexId: null, redundant: false, pre: data.pre, post: data.pre, children: [data],
  };

  const root = d3.hierarchy<TreeNode>(start, (d) => d.children);

  // Nodes in pre-order (the engine's exploration order)
  const allNodes: LaidOutNode[] = [];
  root.eachBefore((node) => allNodes.push(node as LaidOutNode));

  // Precompute node parameters before rendering
  allNodes.forEach((d) => {
    const { name, arg, result } = d.data;
    const mark = (result && { "Match": " ✓", "Mismatch": " ✗" }[result]) ?? "";
    d.label = { name, arg, mark };
    d.shape = SHAPE[name] ?? "round";
    d.width = shapeWidth(d.shape, name.length + arg.length + mark.length);
  });

  d3.tree<TreeNode>()
    .nodeSize([1, DEPTH_GAP])
    .separation((a, b) => ((a as LaidOutNode).width + (b as LaidOutNode).width) / 2 + PADDING)(root);

  container.replaceChildren();
  const W = container.clientWidth || FALLBACK_W;
  const H = container.clientHeight || FALLBACK_H;
  const svg = d3
    .select(container)
    .append("svg")
    .attr("class", "tree-svg")
    .attr("width", W)
    .attr("height", H);
  const view = svg
    .append("g");

  const mayPan = (e: any) =>
    e.button === 0 && (e.type === "wheel" ||
      (e.target as Element).closest(".tnode") === null);

  const zoom = d3
    .zoom<SVGSVGElement, unknown>()
    .scaleExtent([MIN_ZOOM, MAX_ZOOM])
    .extent([[0, 0], [W, H]])
    .filter(mayPan)
    .on("start", () => svg.classed("panning", true))
    .on("zoom", (e) => view.attr("transform", e.transform))
    .on("end", () => svg.classed("panning", false));
  svg.call(zoom);

  view
    .append("g")
    .selectAll("path")
    .data(root.links() as HierarchyPointLink<TreeNode>[])
    .join("path")
    .attr("class", "tedge")
    .attr("data-regex-id",  (d) =>
      (d.target as LaidOutNode).data.regexId)
    .attr("data-redundant", (d) =>
      (d.target as LaidOutNode).data.redundant ? "" : null)
    .attr("data-has-ghost", (d) =>
      d.source.data.hasGhostSubtree && d.source.children?.[0] === d.target ? "" : null)
    .attr("d", d3.linkVertical<HierarchyPointLink<TreeNode>, LaidOutNode>()
      .x((d) => d.x)
      .y((d) => d.y));

  const nodes = view
    .append("g")
    .selectAll<SVGGElement, LaidOutNode>("g")
    .data(allNodes)
    .join("g")
    .attr("class", "tnode")
    .attr("data-kind", (d) => d.data.name)
    .attr("data-status", (d) => d.data.result)
    .attr("data-regex-id", (d) => d.data.regexId)
    .attr("data-redundant", (d) => d.data.redundant ? "" : null)
    .attr("transform", (d) => `translate(${d.x},${d.y})`)
    .on("mouseenter", (e, _) => { onHover(e.currentTarget); })
    .on("mouseleave", () => onHover(null))
    .on("click", (e) => { onClick(e.currentTarget); });

  nodes.each(function (d) { drawShape(this, d); });

  const txt = nodes.append("text").attr("dy", "0.3em");
  for (const part of ["name", "arg", "mark"] as const)
    txt.append("tspan")
      .attr("class", "tlabel")
      .attr("data-part", part)
      .text((d) => d.label[part]);

  const fit = (): void => {
    const w = container.clientWidth || FALLBACK_W;
    const h = container.clientHeight || FALLBACK_H;
    svg.attr("width", w).attr("height", h);
    zoom.extent([[0, 0], [w, h]]);
    const b = (view.node() as SVGGElement).getBBox();
    const k = Math.min(MAX_FIT_SCALE, FIT_MARGIN * Math.min(w / b.width, h / b.height));
    svg.call(
      zoom.transform,
      d3.zoomIdentity
        .translate(w / 2 - k * (b.x + b.width / 2), NODE_HEIGHT - k * b.y)
        .scale(k),
    );
  };

  fit();
  return fit;
}
