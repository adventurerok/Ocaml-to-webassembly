
const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);
const exec = util.promisify(require('child_process').exec);

const {testFatal, testFailure} = require("./util");
const {testBenchmarks} = require("./benchmarks");


const wat2wasmPath = "wat2wasm";
const compilerPath = "_build/default/toplevel.exe";

// Global arguments
let samplesDir = "samples/";
let debug = false;
let noCompile = false;
let otwaArgs = "";

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
  if(otwaArgs.length > 0) {
    command += " " + otwaArgs;
  }

  if(debug) {
    console.log("exec otwa for " + test.path + ": " + command);
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
    await testFunctions(test);
    await testBenchmarks(test, benchOptions);
  } catch(e) {
    let detail = e.detail;
    if(e.message === "unreachable") {
      e.detail = e;
    }

    return {
      path: path,
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


async function testFunctions(test) {
  if(!test.instance || !test.json || !test.json.functions) return;

  for(let funcTest in test.json.functions) {
    let funcName = funcTest.substring(0, funcTest.indexOf("("));
    let argPart = funcTest.substring(funcTest.indexOf("(") + 1, funcTest.indexOf(")"));

    let args = argPart.split(",");

    let waArgs = [];
    for(let arg of args) {
      if(arg.endsWith("f")) {
        waArgs.push(parseFloat(arg.substring(0, arg.length - 1)));
      } else {
        waArgs.push(parseInt(arg));
      }
    }

    let waFunc = test.instance.exports[funcName];

    try {
      let result = waFunc(...waArgs);
      let expected = test.json.functions[funcTest].toString();

      if(!compareValues(test.instance, expected, result)) {
        testFailure(test, "Unexpected function result for " + funcTest + ": expected " + expected + " but got " + result);
      }
    } catch(e) {
      testFailure(test, "Failed function evaluation", e);
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


let onlyAllow = undefined;

let benchOptions = {
  benchStats: false,
  benchMult: 1,
  benchStatCount: 3,
  otwaOnly: false,
};

console.log("OTWA E2E tester params: " + process.argv.slice(2).join(" "));

for(let argIndex = 2; argIndex < process.argv.length; ++argIndex) {
  let arg = process.argv[argIndex];

  if(arg.startsWith("-")) {
    switch(arg) {
      case "-nocompile":
        noCompile = true;
        break;
      case "-e2edebug":
        debug = true;
        break;
      case "-benchstat":
        benchOptions.benchStats = true;
        console.log("Benchmark stats mode enabled");

        benchOptions.benchStatCount = parseInt(process.argv[argIndex + 1]);
        ++argIndex;

        break;
      case "-only":
        onlyAllow = process.argv[argIndex + 1];
        ++argIndex;
        break;

      case "-benchmult":

        benchOptions.benchMult = parseInt(process.argv[argIndex + 1]);
        ++argIndex;

        break;

      case "-otwaonly":
        benchOptions.otwaOnly = true;
        break;

      default:
        // otwa compiler argument
        if(otwaArgs.length > 0) {
          otwaArgs += " ";
        }
        otwaArgs += arg;
        if(debug) {
          console.log(arg);
        }
    }
  } else {
    samplesDir = arg;
  }
}

const run = async () => {
  const samplesFiles = fs.readdirSync(samplesDir).filter((name) => {
    if(onlyAllow) {
      let dotIndex = name.indexOf(".");
      if (dotIndex < 0) return false;

      if(name.substring(0, dotIndex) != onlyAllow) {
        return false;
      }
    }

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
