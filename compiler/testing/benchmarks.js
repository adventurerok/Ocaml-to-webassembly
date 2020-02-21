const {testFatal} = require("./util");

const util = require('util');
const fs = require("fs");

const readFile = util.promisify(fs.readFile);
const exec = util.promisify(require('child_process').exec);



module.exports.testBenchmarks = async function(test) {
  if(!test.instance || !test.json || !test.json.benchmarks) return;

  test.benchmarks = {};

  // benchmark
  for(let benchName in test.json.benchmarks) {
    if(!test.json.benchmarks.hasOwnProperty(benchName)) continue;

    test.benchmarks[benchName] = {};
    let bench = test.json.benchmarks[benchName];
    bench.name = benchName;

    // run all benchmarks
    let promises = [];
    promises.push(otwaBenchmark(test, bench));
    promises.push(interpBenchmark(test, bench));

    await Promise.all(promises);

    let resultStrings = [];
    for(let targetName in test.benchmarks[benchName]) {
      if(!test.benchmarks[benchName].hasOwnProperty(targetName)) continue;

      resultStrings.push(targetName + " = " + test.benchmarks[benchName][targetName] + "ms");
    }

    test.benchResults.push(benchName + ": " + resultStrings.join(", "));

  }

};

async function otwaBenchmark(test, bench) {
  let start = (new Date()).getTime();
  for(let i = 0; i < bench.iterations; i++) {
    test.instance.exports[bench.func](0);
  }
  test.benchmarks[bench.name].otwa = ((new Date()).getTime() - start) / bench.iterations;
}

async function interpBenchmark(test, bench) {
  let ocamlEcho = "let start = Sys.time() in let () = (for iter = 1 to "
    + bench.iterations + " do " + bench.func + "() done) in Sys.time() -. start;;";
  let ocamlCmd = "echo \"" + ocamlEcho + "\" | ocaml -init " + test.path;

  let ocamlTime = 0;

  try {
    let res = await exec(ocamlCmd);
    let regex = /^- : float = ([0-9]+\.[0-9]+(?:e-[0-9]+)?)$/gm;
    let regMatch = regex.exec(res.stdout);
    ocamlTime = parseFloat(regMatch[1]) * 1000 / bench.iterations;
  } catch(e) {
    testFatal(test, "Failed OCaml REPL Benchmark", e.stderr);
  }

  test.benchmarks[bench.name].interp = ocamlTime;
}