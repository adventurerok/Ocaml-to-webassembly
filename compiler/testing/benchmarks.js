const {testFatal} = require("./util");

const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);
const writeFile = util.promisify(fs.writeFile);
const exec = util.promisify(require('child_process').exec);


module.exports.testBenchmarks = async function (test, options) {
  if (!test.instance || !test.json || !test.json.benchmarks) return;

  test.benchmarks = {};

  // compile list of benchmarks
  let benchmarks = [];
  for (let benchName in test.json.benchmarks) {
    if (!test.json.benchmarks.hasOwnProperty(benchName)) continue;

    test.benchmarks[benchName] = {};
    let bench = test.json.benchmarks[benchName];
    bench.name = benchName;

    benchmarks.push(bench);
  }

  if(options.benchStats) {
    await statsBenchmarks(test, benchmarks, options);
  } else {
    await nonStatsBenchmarks(test, benchmarks, options);
  }

};

async function nonStatsBenchmarks(test, benchmarks, options) {
  // start the compiled ones first
  let compiledPromise = compiledBenchmarks(test, benchmarks, options);

  for (let bench of benchmarks) {
    // run all benchmarks
    let promises = [];
    promises.push(otwaBenchmark(test, bench, options));
    promises.push(interpBenchmark(test, bench, options));

    await Promise.all(promises);

  }

  // wait for the compiled ones
  await compiledPromise;

  for (let benchName in test.benchmarks) {
    if (!test.benchmarks.hasOwnProperty(benchName)) continue;

    let resultStrings = [];
    let targetNames = Object.keys(test.benchmarks[benchName]).sort();
    for (let targetName of targetNames) {
      let benchData = test.benchmarks[benchName][targetName];

      if(benchData.time !== undefined) {
        resultStrings.push(targetName + " = " + benchData.time.toPrecision(3) + "ms & " + formatBytes(benchData.memory, 4));
      } else {
        resultStrings.push(targetName + " = " + benchData.toPrecision(3) + "ms");
      }
    }

    test.benchResults.push(benchName + ": " + resultStrings.join(", "));

  }

}

async function statsBenchmarks(test, benchmarks, options) {
  await prepareCompiledBenchmarks(test, benchmarks, options);

  let allBenchmarks = [];

  for(let count = 0; count < options.benchStatCount; count++) {
    test.benchmarks = {};

    for(let bench of benchmarks) {
      test.benchmarks[bench.name] = {};
    }

    let compiledPromise = execCompiledBenchmarks(test, benchmarks, options);

    for (let bench of benchmarks) {
      // run all benchmarks
      let promises = [];
      promises.push(otwaBenchmark(test, bench, options));
      promises.push(interpBenchmark(test, bench, options));

      await Promise.all(promises);

    }

    await compiledPromise;

    allBenchmarks.push(test.benchmarks);
  }

  for (let benchName in test.benchmarks) {
    if(!test.benchmarks.hasOwnProperty(benchName)) continue;

    let resultStrings = [];
    let targetNames = Object.keys(allBenchmarks[0][benchName]).sort();

    for(let targetName of targetNames) {
      let timePoints = [];
      let memoryPoints = [];

      for(let count = 0; count < options.benchStatCount; count++) {
        let benchData = allBenchmarks[count][benchName][targetName];
        if(benchData.time !== undefined) {
          timePoints.push(benchData.time / options.benchMult);
          memoryPoints.push(benchData.memory / options.benchMult);
        } else {
          timePoints.push(benchData / options.benchMult);
        }
      }

      if(timePoints.length > 0) {
        let stats = statsOfPoints(timePoints);

        test.benchResults.push([benchName, targetName, "time", stats.min, stats.oneBelow, stats.avg, stats.oneAbove, stats.max, stats.stdDev].join(","));
      }

      if(memoryPoints.length > 0) {
        let stats = statsOfPoints(memoryPoints);

        test.benchResults.push([benchName, targetName, "memory", stats.min, stats.oneBelow, stats.avg, stats.oneAbove, stats.max, stats.stdDev].join(","));
      }
    }
  }
}

function statsOfPoints(points) {
  if(points.length === 0) {
    return undefined;
  }

  let sum = points.reduce((x,y) => x + y, 0);
  let avg = sum / points.length;
  let sumSq = points.reduce((x,y) => x + y * y, 0);

  let min = Math.min(...points);
  let max = Math.max(...points);

  let variance = (sumSq / points.length) - (avg * avg);
  let stdDev = Math.sqrt(variance);

  return {
    min: min,
    max: max,
    avg: avg,
    variance: variance,
    stdDev: stdDev,
    oneBelow: Math.max(avg - stdDev, min),
    oneAbove: Math.min(avg + stdDev, max)
  };
}

async function otwaBenchmark(test, bench, options) {
  let start = (new Date()).getTime();

  let startMemory = test.instance.exports.mem_idx.value;

  const iters = bench.iterations * options.benchMult;

  for (let i = 0; i < iters; i++) {
    test.instance.exports[bench.func](0);
  }

  let endMemory = test.instance.exports.mem_idx.value;
  let usedMemory = endMemory - startMemory;

  // Sneaky, but for the purpose of benchmark should prevent repeated benchmarks running OOM
  test.instance.exports.mem_idx.value = startMemory;

  test.benchmarks[bench.name].otwa = {
    time: ((new Date()).getTime() - start),
    memory: usedMemory
  };
}

async function interpBenchmark(test, bench, options) {
  if(options.otwaOnly) return;

  let iters = bench.iterations * options.benchMult;

  let ocamlEcho = "let start = Sys.time() in let () = (for iter = 1 to "
    + iters + " do " + bench.func + "() done) in Sys.time() -. start;;";
  let ocamlCmd = "echo \"" + ocamlEcho + "\" | ocaml -init " + test.path;

  let ocamlTime = 0;

  try {
    let res = await exec(ocamlCmd);
    let regex = /^- : float = ([0-9]+\.[0-9]+(?:e-[0-9]+)?)$/gm;
    let regMatch = regex.exec(res.stdout);
    ocamlTime = parseFloat(regMatch[1]) * 1000;
  } catch (e) {
    testFatal(test, "Failed OCaml REPL Benchmark", e.stderr);
  }

  test.benchmarks[bench.name].interp = ocamlTime;
}


async function prepareCompiledBenchmarks(test, benchmarks, options) {
  if(options.otwaOnly) return;

  let testCode = await readFile(test.path);

  let letStatements = benchmarks.map(compiledLetBenchmark(options));

  let fullCode = testCode + "\n" + letStatements.join("\n\n");

  let benchPath = test.pathWithoutExtension + ".bench";

  await writeFile(benchPath + ".ml", fullCode);

  try {
    let compileOpt = exec("ocamlopt " + benchPath + ".ml -o " + benchPath + ".exe");

    // Js_of_ocaml depends on the bytecode, so do those in order
    await exec("ocamlc " + benchPath + ".ml -o " + benchPath + ".byte");
    await exec("js_of_ocaml " + benchPath + ".byte");
    await compileOpt;
  } catch (e) {
    testFatal(test, "Failed other compiler compilation", e.stderr);
  }
}

async function execCompiledBenchmarks(test, benchmarks, options) {
  if(options.otwaOnly) return;

  let benchPath = test.pathWithoutExtension + ".bench";

  let benchByte = execBenchmarkProgram(test, "byte", "ocamlrun " + benchPath + ".byte");
  let benchJs = execBenchmarkProgram(test, "js", "node " + benchPath + ".js");
  let benchOpt = execBenchmarkProgram(test, "opt", benchPath + ".exe");

  await Promise.all([benchByte, benchJs, benchOpt]);
}

async function compiledBenchmarks(test, benchmarks, options) {
  await prepareCompiledBenchmarks(test,  benchmarks, options);

  return execCompiledBenchmarks(test, benchmarks, options);
}

async function execBenchmarkProgram(test, targetName, cmd) {

  try {
    let res = await exec(cmd);
    let lines = res.stdout.split("\n");
    for (let line of lines) {
      if (line.length === 0) continue;

      let parts = line.split(" ");
      let benchName = parts[0];
      test.benchmarks[benchName][targetName] = parseFloat(parts[1]) * 1000;
    }
  } catch (e) {
    testFatal(test, "Failed execution of compiled benchmark: " + cmd, e.stderr);
  }
}

function compiledLetBenchmark(options) {
  return bench => {
    let iters = bench.iterations * options.benchMult;

    let firstLine = "let () = (let start = Sys.time() in let () = (for iter_c = 1 to " + iters + " do ";
    let secondLine = "(let _ = " + bench.func + "() in ()) done) in let time = Sys.time() -. start in ";
    let thirdLine = "print_endline (\"" + bench.name + " \" ^ (string_of_float time)));;";

    return firstLine + secondLine + thirdLine;
  }
}

function formatBytes(amount, precision) {
  if (amount >= 1024 * 1024 * 1024) {
    const gbAmount = amount / (1024 * 1024 * 1024);
    return gbAmount.toPrecision(precision) + " GiB";
  } else if(amount >= 1024 * 1024) {
    const mbAmount = amount / (1024 * 1024);
    return mbAmount.toPrecision(precision) + " MiB";
  } else if(amount >= 1024) {
    const kbAmount = amount / 1024;
    return kbAmount.toPrecision(precision) + " KiB";
  } else {
    return amount.toPrecision(precision) + " B";
  }
}