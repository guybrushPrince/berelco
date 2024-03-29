<?php
ini_set('memory_limit', '4096M');

include_once "Xml2Array.php";
include_once "Model.php";
include_once "Util.php";
include_once "Parser.php";
include_once "RunNetsAlgo.php";
include_once "BeRelCoAlgo.php";

// Set the file format depending on the "json" parameter.
$fileType = ".pnml";
$json = false;
if (in_array("json", $argv)) {
	$fileType = ".json";
	$json = true;
    // soundSAP.php defines all nets being sound in SAP.
	include_once "soundSAP.php";
} else {
    // sound.php defines all nets being sound in IBM.
	include_once "sound.php";
}

// Produce a DOT-output of the net.
$dot = in_array("dot", $argv);
$without = in_array("without", $argv);

$arguments = array_values(array_diff($argv, ["json", "dot", "without"]));
 
$files = [];
$folder = $arguments[1];
if (strpos($folder, $fileType) > 0) {
    // It is a single file, which is considered as sound.
	$files = [ $folder ];
	$sound = array_map(function (string $file) { return basename($file); }, $files);
} else Util::determineFiles($folder, $files, $fileType);

// Define the output CSV file.
if (count($arguments) >= 3) {
	$out = $arguments[2];
} else {
	$out = "times.csv";
}

$results = [];
foreach ($files as $file) {
    // Ignore unsound process models.
	if (!in_array(basename($file), $sound)) continue;
	$content = file_get_contents($file);
	if (!$json) {
		$xml = (new Xml2Array())->parse($content);
	 
		$nets = Parser::parsePNMLArray($xml);
		Parser::determinePrePostSets($nets);
	} else {
		$nets = Parser::parseJSON($content);
	}
	
	foreach ($nets as $nr => $net) {
		if (!$without) echo $file . PHP_EOL;

        // Ignore cyclic nets yet.
		$acyclic = !Parser::isCyclic($net);
		if (!$acyclic) {
			continue;
		}
		// Produce a DOT output.
		if ($dot) file_put_contents($file . '.dot', Util::toDot($net));
		
		$runNetsAlgo = new RunNetsAlgo();
		$ts = microtime(true);
		$insRelations = $runNetsAlgo->compute($net);
		$tRunNets = microtime(true) - $ts;
					
		$BeRelCo = new BeRelCoAlgo();
		$ts = microtime(true);
		$relations = $BeRelCo->computeAcyclicBehavioralRelations($net);
		$tBeRelCo = microtime(true) - $ts;
		
		/* TEST */
		if (!array_key_exists("intractable", $insRelations)) {
			foreach ($net->places + $net->transitions as $xi => $x) {
				$iR = $insRelations["can co-occur"];
				$bR = $relations["can co-occur"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Can co-occur (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Can co-occur (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["can conflict"];
				$bR = $relations["can conflict"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Can conflict (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Can conflict (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["existential causality"];
				$bR = $relations["existential causality"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Causality (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Causality (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["existential concurrency"];
				$bR = $relations["existential concurrency"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Concurrency (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Concurrency (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["total conflict"];
				$bR = $relations["total conflict"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Total conflict (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Total conflict (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["total co-occur"];
				$bR = $relations["total co-occur"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Total co-occur (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Total co-occur (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["requires"];
				$bR = $relations["requires"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Requires (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Requires (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
				
				$iR = $insRelations["independent"];
				$bR = $relations["independent"];
				if (count(array_diff_key($iR[$xi], $bR[$xi])) > 0) {
					echo "Independent (iR, not in bR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($iR[$xi], $bR[$xi]));
				}
				if (count(array_diff_key($bR[$xi], $iR[$xi])) > 0) {
					echo "Independent (bR, not in iR): " . $xi . PHP_EOL;
					Util::printSet(array_diff_key($bR[$xi], $iR[$xi]));
				}
			}
		}
		/* END TEST */
		
		$results[] = [
			"file" => $file,
			"net"  => $nr + 1,
			"places" => count($net->places),
			"transitions" => count($net->transitions),
			"nodes" => count($net->places + $net->transitions),
			"flows" => count($net->flows),
			"cyclic" => !$acyclic ? "TRUE" : "FALSE",
			//"relations" => count($BeRelCoRes),
			"BeRelCo" => sprintf('%f', $tBeRelCo),
			"BeRelCoNodes" => $BeRelCo->getVisitedNodes(),
			"InstanceAlgo" => sprintf('%f', $tRunNets),
			"InstanceNodes" => $runNetsAlgo->getVisitedNodes(),
			"nr_instances" => $runNetsAlgo->numberRunNets,
			"nodes.has.paths" => $BeRelCo->visitedNodesHasPath,
			"existential concurrency" => array_reduce($relations["existential concurrency"], function(int $s, array $a) { return $s + count($a); }, 0),
			"total concurrency"       => array_reduce($relations["total concurrency"      ], function(int $s, array $a) { return $s + count($a); }, 0),
			"existential causality"   => array_reduce($relations["existential causality"  ], function(int $s, array $a) { return $s + count($a); }, 0),
			"total causality"         => array_reduce($relations["total causality"        ], function(int $s, array $a) { return $s + count($a); }, 0),
			"can conflict"            => array_reduce($relations["can conflict"           ], function(int $s, array $a) { return $s + count($a); }, 0),
			"total conflict"          => array_reduce($relations["total conflict"         ], function(int $s, array $a) { return $s + count($a); }, 0),
			"can co-occur"            => array_reduce($relations["can co-occur"           ], function(int $s, array $a) { return $s + count($a); }, 0),
			"total co-occur"          => array_reduce($relations["total co-occur"         ], function(int $s, array $a) { return $s + count($a); }, 0),
			"requires"                => array_reduce($relations["requires"               ], function(int $s, array $a) { return $s + count($a); }, 0),
			"independent"             => array_reduce($relations["independent"            ], function(int $s, array $a) { return $s + count($a); }, 0),
			"timeExistConcurrency"    => $BeRelCo->timeExistConcurrency,
	        "timeExistCausality"      => $BeRelCo->timeExistCausality,
	        "timeCanCooccur"          => $BeRelCo->timeCanCoOccur,
	        "timeActivatingNodes"     => $BeRelCo->timeTriggers,
	        "timeDependsOn"           => $BeRelCo->timeCannotConflict,
	        "timeTotalCooccurrence"   => $BeRelCo->timeTotalCoOccurrence,
	        "timeCanTotalConflict"    => $BeRelCo->timeCanTotalConflict,
	        "timeRequires"            => $BeRelCo->timeRequires,
	        "timeIndependent"         => $BeRelCo->timeIndependent,
	        "visitedExistConcurrency" => $BeRelCo->visitedExistConcurrency,
	        "visitedExistCausality"   => $BeRelCo->visitedExistCausality,
	        "visitedCanCooccur"       => $BeRelCo->visitedCanCoOccur,
	        "visitedActivatingNodes"  => $BeRelCo->visitedTriggers,
	        "visitedDependsOn"        => $BeRelCo->visitedCannotConflict,
	        "visitedTotalCooccurrence"=> $BeRelCo->visitedTotalCoOccurrence,
	        "visitedCanTotalConflict" => $BeRelCo->visitedCanTotalConflict,
	        "visitedRequires"         => $BeRelCo->visitedRequires,
	        "visitedIndependent"      => $BeRelCo->visitedIndependent,
			"insIntractable"		  => array_key_exists("intractable", $insRelations),
			"inclusive"               => array_sum(array_map(function(Transition $t) { return $t->simulatesOR ? 1 : 0; }, $net->transitions))
		];
	}
	
	unset($nets);
	unset($xml);
	unset($content);
}

// Produce the CSV output file.
if (count($results) >= 1) {
	$first = $results[0];
	$csv = implode(";", array_keys($first)) . PHP_EOL;
	$csv .= implode(PHP_EOL, array_map(function (array $r) {
		return implode(";", $r);
	}, $results));
	file_put_contents($out, $csv);
}
?>