
let globals = undefined;

function loadWasm(path) {
  fetch(path + ".wasm").then(response =>
    response.arrayBuffer()
  ).then(bytes =>
    WebAssembly.instantiate(bytes)
  ).then(results =>
    globals = results.instance.exports
  )
}