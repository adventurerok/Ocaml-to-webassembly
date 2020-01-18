
const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);

// The instance to play around with
let inst = null;
let globals = null;

async function loadFile(path) {
  const buffer = await readFile(path);
  const module = await WebAssembly.compile(buffer);
  const instance = await WebAssembly.instantiate(module);

  inst = instance;
  globals = instance.exports;

  console.log("Loaded WASM successfully");
}
