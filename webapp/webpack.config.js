/** Webpack configuration for @webapp/bundle */
const path = require("path");
const fs = require("fs");

const buildDir = __dirname; // /_build/…/webapp/
const sourceDir = path.resolve(buildDir, "../../../webapp"); // /webapp
const npmDir = path.join(sourceDir, "node_modules"); // /webapp/node_modules
const melangeDir = path.resolve(buildDir, "app/node_modules"); // /_build/…/webapp/app/node_modules
const tsConfig = path.resolve(sourceDir, "tsconfig.json");

// Tell chrome how to edit our source files
const devtoolsPath = ".well-known/appspecific";
const devtoolsJSON = { workspace: { root: sourceDir, uuid: "9f2c1d7e-4b6a-4c2e-8a1f-3d5e7b9c0a11" } };
class DevToolsWorkspacePlugin {
  apply(compiler) {
    compiler.hooks.afterEmit.tap("DevToolsWorkspace", () => {
      const dir = path.join(compiler.outputPath, devtoolsPath);
      fs.mkdirSync(dir, { recursive: true });
      const fpath = path.join(dir, "com.chrome.devtools.json");
      fs.writeFileSync(fpath, JSON.stringify(devtoolsJSON));
    });
  }
}

const tsRule = {
  test: /[.]mts$/,
  loader: "ts-loader",
  resolve: { extensionAlias: { ".mjs": [".mts", ".mjs"] } }, // some .mjs imports are .mts sources
  options: {
    configFile: tsConfig,
    onlyCompileBundledFiles: true,
    compilerOptions: { // ts runs from _build/, which has no node_modules
      typeRoots: [path.join(npmDir, "@types")],
    },
  },
}

const jsRule = {
  test: /[.]m?js$/,
  type: "javascript/auto",
  resolve: { fullySpecified: false }
}

module.exports = (env) => ({
  mode: env.profile === "release" ? "production" : "development",
  target: "web",
  devtool: "source-map",
  output: { filename: "linden-viz.js" },
  resolve: { modules: [melangeDir, npmDir] },
  resolveLoader: { modules: [npmDir] },
  module: { rules: [tsRule, jsRule] },
  plugins: env.profile === "release" ? [] : [new DevToolsWorkspacePlugin()],
  performance: { hints: false },
});
