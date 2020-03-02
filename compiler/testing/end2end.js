
const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);
const exec = util.promisify(require('child_process').exec);

const {testFatal, testFailure} = require("./util");
const {testBenchmarks} = require("./benchmarks");

let samplesDir = "samples/";

const wat2wasmPath = "wat2wasm";
const compilerPath = "_build/default/toplevel.exe";

const debug = false;

async function createTestObject(path) {
  let pathWithoutExtension = path.substring(0, path.lastIndexOf("."));

  let result = {};
  result.path = path;
  result.pathWithoutExtension = pathWithoutExtension;
  result.failures = [];
  result.benchResults = [];

  let testFileContents;
  try {
    testFileContents = await readFile(pathWithoutExtension + ".json", "utf8");
  } catch(e) {}

  if(testFileContents) {
    result.json = JSON.parse(testFileContents);
  }

  return result;
}

async function testCompileAndInstantiate(test) {

  // Compile to wast
  let wastPath = test.pathWithoutExtension + ".wast";
  let command = compilerPath + " " + test.path + " -output " + wastPath;

  if(debug) {
    console.log("exec otwa for " + test.path);
  }

  try{
    if(!noCompile) {
      await exec(command);
    }
  } catch(e) {
    testFatal(test, "Failed otwa compilation", e.stdout + "\n" + e.stderr);
  }

  // Compile to wasm
  let wasmPath = test.pathWithoutExtension + ".wasm";

  if(debug) {
    console.log("exec wat2wasm for " + test.path);
  }

  try{
    await exec(wat2wasmPath + " " + wastPath + " -o " + wasmPath);
  } catch(e) {
    testFatal(test, "Failed wasm compilation", e.stderr);
  }

  if(debug) {
    console.log("instantiate for " + test.path);
  }

  // instantiate wasm
  try{
    const buffer = await readFile(wasmPath);
    test.module = await WebAssembly.compile(buffer);
    test.instance = await WebAssembly.instantiate(test.module);
  } catch(e) {
    testFatal(test, "Failed WebAssembly instantiation", e);
  }

  if(debug) {
    console.log("instantiated for " + test.path);
  }
}

async function testFile(path) {
  let test = await createTestObject(path);

  try {
    await testCompileAndInstantiate(test);
    await testGlobals(test);
    await testBenchmarks(test);
  } catch(e) {
    return {
      path: e.path,
      result: false,
      message: e.message,
      detail: e.detail
    }
  }

  if(test.failures.length !== 0) {
    let failMsgs = [];
    for(let fail of test.failures) {
      let msg = fail.message + "\n";
      if(fail.detail) {
        msg += "Detail: " + fail.detail + "\n\n";
      }
      failMsgs.push(msg);
    }

    return {
      path: path,
      result: false,
      message: test.failures.length + " failures",
      detail: failMsgs.join(""),
      bench: test.benchResults
    };
  }

  return {
    path: path,
    result: true,
    bench: test.benchResults
  }
}

async function testGlobals(test) {
  if(!test.instance || !test.json || !test.json.globals) return;

  for(let global in test.json.globals) {
    let expected = test.json.globals[global].toString();

    let glob_object = test.instance.exports["global_" + global];
    if(!glob_object) {
      testFailure(test, "Missing global value '" + global + "'");
    } else {
      let actual = glob_object.value;

      if(!compareValues(test.instance, expected, actual)) {
        testFailure(test, "Mismatch in global value '" + global + "': expected " + expected + " but got " + actual);
      }
    }
  }

}

function compareValues(instance, expected, actual) {
  if(expected === "true") {
    return actual === 1;
  } else if(expected === "false") {
    return actual === 0;
  } else if(expected.endsWith("f")) {
    // float equality test
    const precision = 6;
    expected = Number.parseFloat(expected.substring(0, expected.length - 1)).toPrecision(precision);
    actual = Number.parseFloat(actual).toPrecision(precision);
    return expected === actual;
  } else {
    // default integer test, but use parseFloat to avoid parseInt just ignoring floating point part
    return Number.parseFloat(expected) === actual;
  }
}

let canExit = false;

let promises;
let allPromise;

let noCompile = false;

if(process.argv.length > 2) {
  samplesDir = process.argv[2];
}

if(process.argv.length > 3) {
  noCompile = true;
}

const run = async () => {
  const samplesFiles = fs.readdirSync(samplesDir).filter((name) => {
    return name.endsWith(".ml") && !name.endsWith(".bench.ml");
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

    for(let result of fullResults) {
      if(result.bench && result.bench.length > 0) {
        console.log("\n");
        console.log("Benchmarks for " + result.path);
        for(let benchItem of result.bench) {
          console.log(benchItem);
        }
      }
    }
  } else {
    console.log("Failure! See above for details!");
  }

  canExit = true;
};

let mainPromise = run();

function wait () {
  if(!canExit) {
    setTimeout(wait, 100);
  }
}

wait();
