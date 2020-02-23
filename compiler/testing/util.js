
function testFailure(test, message, detail) {
  if(!test.failures) {
    test.failures = [];
  }

  test.failures.push({
    message,
    detail
  });
}
module.exports.testFailure = testFailure;

module.exports.testFatal = function(test, message, detail) {
  testFailure(test, message, detail);

  throw {
    path: test.path,
    message,
    detail
  }
};

