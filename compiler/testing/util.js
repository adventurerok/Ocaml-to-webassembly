
module.exports.testFailure = async function(test, message, detail) {
  if(!test.failures) {
    test.failures = [];
  }

  test.failures.push({
    message,
    detail
  });
};

module.exports.testFatal = async function(test, message, detail) {
  testFailure(test, message, detail);

  throw {
    path: test.path,
    message,
    detail
  }
};

