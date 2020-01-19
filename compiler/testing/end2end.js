
const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);
const exec = util.promisify(require('child_process').exec);

const samplesDir = "samples/"

const wat2wasmPath = "wat2wasm"
const compilerPath = "_build/default/toplevel.exe"

const debug = false;

async function testFile(path) {
  let pathWithoutExtension = path.substring(0, path.lastIndexOf("."));
  let wastPath = pathWithoutExtension + ".wast";

  // Compile to wast
  let command = compilerPath + " " + path + " -output " + wastPath;

  if(debug) {
    console.log("exec otwa for " + path);
  }

  try{
    await exec(command);
  } catch(e) {
    return {
      path: path,
      result: false,
      message: "Failed otwa compilation",
      detail: e.stdout + "\n" + e.stderr
    }
  }

  // Compile to wasm
  let wasmPath = pathWithoutExtension + ".wasm";

  if(debug) {
    console.log("exec wat2wasm for " + path);
  }

  try{
    await exec(wat2wasmPath + " " + wastPath + " -o " + wasmPath);
  } catch(e) {
    return {
      path: path,
      result: false,
      message: "Failed wasm compilation",
      detail: e.stderr
    };
  }

  if(debug) {
    console.log("instantiate for " + path);
  }

  // instantiate wasm
  const buffer = await readFile(wasmPath);
  const module = await WebAssembly.compile(buffer);
  const instance = await WebAssembly.instantiate(module);

  if(debug) {
    console.log("instantiated for " + path);
  }

  let testFileContents;

  try {
    testFileContents = await readFile(pathWithoutExtension + ".json", "utf8");
  } catch(e) {}

  if(testFileContents) {
    const testJson = JSON.parse(testFileContents);

    return runInstanceTests(path, instance, testJson);
  } else {
    console.log("No json for " + path);
    return {
      path: path,
      result: true
    }
  }
}

function runInstanceTests(path, instance, testJson) {
  let failures = [];

  if(testJson.globals) {
    for(let global in testJson.globals) {
      let expected = testJson.globals[global].toString();
      let actual = instance.exports["global_" + global].value;

      if(!compareValues(instance, expected, actual)) {
        failures.push("Mismatch in global value '" + global + "': expected " + expected + " but got " + actual);
      }
    }
  }

  if(failures.length == 0) {
    return {
      path: path,
      result: true
    }
  } else {
    return {
      path: path,
      result: false,
      message: "Failed WebAssembly runtime testing",
      detail: failures.join("\n")
    }
  }
}

function compareValues(instance, expected, actual) {
  if(expected == "true") {
    return actual == 1;
  } else if(expected == "false") {
    return actual == 0;
  } else if(expected.endsWith("f")) {
    // float equality test
    const precision = 6;
    expected = Number.parseFloat(expected.substring(0, expected.length - 1)).toPrecision(precision);
    actual = Number.parseFloat(actual).toPrecision(precision);
    return expected == actual;
  } else {
    // default integer test, but use parseFloat to avoid parseInt just ignoring floating point part
    return Number.parseFloat(expected) == actual;
  }
}

let canExit = false;

let promises;
let allPromise;

const run = async () => {
  const samplesFiles = fs.readdirSync(samplesDir).filter((name) => {
    return name.endsWith(".ml");
  });

  promises = [];

  for (let sampleFile of samplesFiles) {
    const fullPath = samplesDir + sampleFile;

    promises.push(testFile(fullPath));
  }

  console.log("Awaiting test results...");
  allPromise = Promise.all(promises);
  let fullResults = await allPromise;
  console.log("\nResults in...\n");

  let success = true;

  for(let result of fullResults) {
    if(!result.result) {
      success = false;

      console.log("Path failed: " + result.path);
      console.log(result.message);
      console.log(result.detail);
      console.log("\n");
    }
  }

  if(success) {
    console.log("Success! All " + fullResults.length + " tests passed!");
  } else {
    console.log("Failure! See above for details!");
  }

  canExit = true;
}

let mainPromise = run();

function wait () {
  if(!canExit) {
    setTimeout(wait, 100);
  }
}

wait();
