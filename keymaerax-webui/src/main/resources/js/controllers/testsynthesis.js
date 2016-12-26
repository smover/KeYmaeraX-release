angular.module('keymaerax.controllers').controller('TestSynthCtrl',
    function($scope, $uibModalInstance, $http, spinnerService, FileSaver, Blob, userid, modelid) {

  $scope.testsynthdata = {
    modelid: modelid,
    monitorkind: 'controller',
    numInstances: 1,
    timeout: 0,
    kinds: {compliant: true, incompliant: false}, //@todo with definable safety margin
    metric: undefined,
    testCases: {
      plot: undefined,
      caseInfos: undefined
    }
  }

  $scope.testgenerate = function() {
    spinnerService.show('testSynthesisExecutionSpinner')
    $http({method: 'GET',
           url: "user/" + userid + "/model/" + $scope.testsynthdata.modelid + "/testcase/generate/" +
                          $scope.testsynthdata.monitorkind + '/' + $scope.testsynthdata.numInstances + '/' + $scope.testsynthdata.timeout,
           params: {kinds: JSON.stringify($scope.testsynthdata.kinds)}})
      .then(function(response) {
        $scope.testsynthdata.testCases.plot = response.data.plot;
        $scope.testsynthdata.testCases.metric = response.data.metric; //.(html|string|plainString)
        $scope.testsynthdata.testCases.caseInfos = response.data.caseInfos;
      })
      .finally(function() { spinnerService.hide('testSynthesisExecutionSpinner'); });
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
