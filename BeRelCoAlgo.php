<?php
include_once "Algo.php";

class BeRelCoAlgo implements Algo {
	
	private bool $debug = false;
	private int $visitedNodes = 0;
	public int $visitedNodesAlgo = 0;
	public int $visitedNodesDecomposition = 0;
	public int $visitedNodesHasPath = 0;
	public int $visitedNodesDetection = 0;
	public string $timeExistConcurrency;
	public string $timeExistCausality;
	public string $timeCanCooccur;
	public string $timeActivatingNodes;
	public string $timeDependsOn;
	public string $timeTotalCooccurrence;
	public string $timeCanTotalConflict;
	public string $timeRequires;
	public string $timeIndependent;
	public int $visitedExistConcurrency = 0;
	public int $visitedExistCausality = 0;
	public int $visitedCanCooccur = 0;
	public int $visitedActivatingNodes = 0;
	public int $visitedDependsOn = 0;
	public int $visitedTotalCooccurrence = 0;
	public int $visitedCanTotalConflict = 0;
	public int $visitedRequires = 0;
	public int $visitedIndependent = 0;

	/**
	 * New algorithm: Core: The computation of the relations.
	 * @param Net $net The net.
	 * @return array
	 */
	public function compute(Net $net) : array {
		$ts = microtime(true);
		$vis = 0;
		$P = [];
		$this->determineHasPath($net);
		$nodes = $net->places + $net->transitions;
		foreach ($net->transitions as $t) {
			$vis++;
			$tpost = array_values($t->postset);
			for ($i = 0; $i < count($tpost); $i++) {
				$vis++;
				$x = $tpost[$i]; $P[$x->id] = $x; 
				for ($j = 0; $j < count($tpost); $j++) {
					if ($i === $j) continue;
					$vis += 2;
					$y = $tpost[$j]; $P[$y->id] = $y;
					$hasPathsX = array_diff_key($x->reaches, $y->reaches + $this->virtualNodes);
					
					foreach ($hasPathsX as $sX) {
						$vis++;
						$P[$sX->id] = $sX;
						$hasPathsXY = array_diff_key($y->reaches, $sX->reaches + $this->virtualNodes);
						$P[$sX->id]->parallel += $hasPathsXY;						
					}
				}
			}
		}
		/*$R = [];
		foreach ($P as $sX) {
			$vis += 1;
			foreach ($sX->parallel as $sY) {
				$vis += 1;
				if ($sX->isLoopNode) {
					$sX->remarkable[$sX->id . '-' . $sY->id] = [$sX, $sY];
					$R[$sX->id . '-' . $sY->id] = [$sX, $sY];
				} else if ($sY->isLoopNode) {
					$sY->remarkable[$sX->id . '-' . $sY->id] = [$sX, $sY];
					$R[$sX->id . '-' . $sY->id] = [$sX, $sY];
				} else {
					$R[$sX->id . '-' . $sY->id] = [$sX, $sY];
					$R[$sY->id . '-' . $sX->id] = [$sY, $sX];
					unset($sY->parallel[$sX->id]);
				}
			}
		}
		$this->visitedNodes += $vis;
		$this->visitedNodesAlgo += $vis;
		return $R;*/
		$R = [];
		foreach ($nodes as $xi => $x) $R[$xi] = $x->parallel;
		//$R = [];
		/*foreach ($nodes as $xi => $x) $R[$xi] = [];
		foreach ($P as $sX) {
			$vis += 1;
			foreach ($sX->parallel as $sY) {
				$vis += 1;
				/*if ($sX->isLoopNode) {
					$sX->remarkable[$sX->id . '-' . $sY->id] = [$sX, $sY];
					$R[$sX->id . '-' . $sY->id] = [$sX, $sY];
				} else if ($sY->isLoopNode) {
					$sY->remarkable[$sX->id . '-' . $sY->id] = [$sX, $sY];
					$R[$sX->id . '-' . $sY->id] = [$sX, $sY];
				} else {*/
					/*$R[$sX->id][$sY->id] = $sY;
					$R[$sY->id][$sX->id] = $sX;*/
					/*unset($sY->parallel[$sX->id]);
				}*/
/*			}
		}*/
		$ts = (microtime(true) - $ts);
		$this->timeExistConcurrency = $ts;
		if ($this->debug) echo "Concurrency: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedExistConcurrency += $vis;
		return $R;
	}

	/**
	 * New algorithm: Determine all nodes a node has a path to.
	 * @param Net $net The net.
	 * @return void
	 */
	private function determineHasPath(Net $net) : void {
		if ($this->debug) $ts = microtime(true);
		$vis = 0;
		$visited = [];
		$current = $net->ends + [];
		$all = $net->transitions + $net->places;
		do {
			$cur = array_shift($current);
			$vis++;
			
			$postset = $cur->postset;
			$vis += count($postset);
			$process = count(array_diff_key($postset, $visited)) === 0;
			$vis += count($postset);
			
			if ($process) {
				$visited[$cur->id] = $cur->id;
				foreach ($cur->postset as $p) $cur->reaches += $p->reaches;
				$vis += count($cur->postset);
				//if ($cur instanceof Place) {
					$cur->reaches[$cur->id] = $cur;
				//}
				$current = $current + $cur->preset;
			}
		} while (count($current) > 0);
		$this->visitedNodes += $vis;
		$this->visitedNodesHasPath += $vis;
		if ($this->debug) echo "HasPath: " . (microtime(true) - $ts) . PHP_EOL;
	}
	
	/**
	 * Determines the (existential/total) causality relation.
	 * @param Net $net The net.
	 * @return array
	 */
	private function determineCausality(Net $net) : array {
		$ts = microtime(true);
		$vis = 0;
		// Concurrency must have been defined before because of the has-path relation.
		$R = [];
		$nodes = $net->transitions + $net->places;
		foreach ($nodes as $xi => $x) {
			$vis++;
			$R[$xi] = $x->reaches;
			unset($R[$xi][$xi]);
		}
		$ts = (microtime(true) - $ts);
		$this->timeExistCausality = $ts;
		if ($this->debug) echo "Causality: " . $ts . PHP_EOL;
		$this->visitedExistCausality = $vis;
		$this->visitedNodes += $vis;
		return $R;
	}
	
	/**
	 * Determines the can-co-occur relation.
	 * @param Net $net The net.
	 * @param array $concurrency The concurrency relation.
	 * @param array $causality The causality relation.
	 * @return array
	 */
	private function determineCanCooccur(Net $net, array $concurrency, array $causality) : array {
		$ts = microtime(true);
		$vis = 0;
		$R = [];
		$nodes = $net->transitions + $net->places;
		$flipped = [];
		foreach ($nodes as $xi => $x) $flipped[$xi] = [];
		$vis += count($nodes);
		foreach ($causality as $xi => $rel) {
			$vis++;
			foreach ($rel as $yi => $y) {
				$vis++;
				$flipped[$yi][$xi] = $x;
			}
		}
		foreach ($nodes as $xi => $x) {
			$vis++;
			$R[$xi] = $concurrency[$xi] + $causality[$xi] + $flipped[$xi];
		}
		$ts = (microtime(true) - $ts);
		$this->timeCanCooccur = $ts;
		if ($this->debug) echo "Can co-occur: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedCanCooccur = $vis;
		return $R;
	}
	
	/**
	 * Orders the nodes of the net topologically.
	 * @param Net $net The net.
	 * @return array
	 */
	private function topologicalSort(Net $net) : array {
		if ($this->debug) $ts = microtime(true);
		$vis = 0;
		$L = [];
		$S = array_values($net->starts);
		$presets = [];
		foreach ($net->places + $net->transitions as $xi => $x) {
			$vis++;
			$presets[$xi] = $x->preset + [];
		}

		while (count($S) > 0) {
			$vis++;
			$n = array_shift($S);
			$L[] = $n;
			foreach ($n->postset as $mi => $m) {
				$vis++;
				unset($presets[$mi][$n->id]);
				if (count($presets[$mi]) === 0) {
					$S[] = $m;
				}
			}
		}

		if ($this->debug) echo "Topological sort: " . (microtime(true) - $ts) . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedActivatingNodes += $vis;
		return $L;
	}

	/**
	 * Orders the nodes of the net reverse topologically.
	 * @param Net $net The net.
	 * @return array
	 */
	private function reversetopologicalSort(Net $net) : array {
		if ($this->debug) $ts = microtime(true);
		$vis = 0;
		$L = [];
		$S = array_values($net->ends);
		$postsets = [];
		foreach ($net->places + $net->transitions as $xi => $x) {
			$vis++;
			$postsets[$xi] = $x->postset + [];
		}

		while (count($S) > 0) {
			$vis++;
			$n = array_shift($S);
			$L[] = $n;
			foreach ($n->preset as $mi => $m) {
				$vis++;
				unset($postsets[$mi][$n->id]);
				if (count($postsets[$mi]) === 0) {
					$S[] = $m;
				}
			}
		}

		if ($this->debug) echo "Reverse topological sort: " . (microtime(true) - $ts) . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedDependsOn += $vis;
		return $L;
	}
	
	/**
	 * Determines the activating-node relation.
	 * @param Net $net The net.
	 * @return array
	 */
	private function determineActivatingNodes(Net $net) : array {
		$ts = microtime(true);
		$vis = 0;
		$R = [];
		$L = $this->reversetopologicalSort($net);
		while (count($L) > 0) {
			$vis++;
			$x = array_shift($L);
			$tpost = array_keys($x->postset);
			if (count($tpost) > 0) {
				$tmpR = $R[$tpost[0]];
				if ($x instanceof Place || $x->simulatesOR) {
					for ($i = 1; $i < count($tpost); $i++) {
						$tmpR = array_intersect_key($tmpR, $R[$tpost[$i]]);
					}
				} else {
					for ($i = 1; $i < count($tpost); $i++) {						
						$tmpR += $R[$tpost[$i]];
					}
				}
				$vis += count($tpost);
			} else $tmpR = [];
			$tmpR[$x->id] = $x;
			$R[$x->id] = $tmpR;
		}
		$ts = (microtime(true) - $ts);
		$this->timeActivatingNodes = $ts;
		if ($this->debug) echo "Activating nodes: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedActivatingNodes += $vis;
		return $R;
	}
	
	/**
	 * Compute the depends-on relation.
	 * @param Net $net The net.
	 * @param array $activatingNodes The activating-node relation as adjacency list.
	 * @return array
	 */
	private function determineDependsOn(Net $net, array $activatingNodes) : array {
		$ts = microtime(true);
		$vis = 0;
		$R = [];
		$L = $this->topologicalSort($net);
		while (count($L) > 0) {
			$vis++;
			$x = array_shift($L);
			$tpre = array_keys($x->preset);
			if (count($tpre) > 0) {
				$tmpR = $R[$tpre[0]];
				for ($i = 1; $i < count($tpre); $i++) {
					$tmpR = array_intersect_key($tmpR, $R[$tpre[$i]]);
				}
				$vis += count($tpre);
			} else $tmpR = [];
			$tmpR += $activatingNodes[$x->id];				
			$R[$x->id] = $tmpR;
		}
		foreach ($R as $xi => $list) {
			$vis++;
			unset($list[$xi]);
			$R[$xi] = $list;
		}
		$ts = (microtime(true) - $ts);
		$this->timeDependsOn = $ts;
		if ($this->debug) echo "Depends on: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedDependsOn += $vis;
		return $R;		
	}
	
	/**
	 * Compute the total-occurrence relation.
	 * @param Net $net The net.
	 * @param array $dependsOn The depends-on relation as adjacency list.
	 * @return array
	 */
	private function determineTotalCooccurrence(Net $net, array $dependsOn) : array  {
		$ts = microtime(true);
		$vis = 0;
		$R = [];
		$nodes = $net->places + $net->transitions;
		foreach ($nodes as $xi => $x) {
			$vis++;
			$R[$xi] = [];
			$M = $dependsOn[$xi];
			foreach ($M as $yi => $y) {
				$vis++;
				if (array_key_exists($xi, $dependsOn[$yi])) {
					$R[$xi][$yi] = $y;
				}
			}
		}
		$ts = (microtime(true) - $ts);
		$this->timeTotalCooccurrence = $ts;
		if ($this->debug) echo "Total Co-occurrence: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedTotalCooccurrence = $vis;
		return $R;
	}
	
	/**
	 * Compute the missing relations.
	 * @param Net $net The net.
	 * @param array $dependsOn The depends-on relation.
	 * @param array $canCooccur The can-co-occur relation.
	 * @param array $totalCooccur The total co-occurrence relation.
	 * @return array
	 */
	private function determineOthers(Net $net, array $dependsOn, array $canCooccur, array $totalCooccur) : array {
		$vis = 0;
		$visTmp = 0;
		$canConflict = [];
		$totalConflict = [];
		$requires = [];
		$independent = [];
		$nodes = $net->places + $net->transitions;
		$ts = microtime(true);
		foreach ($nodes as $xi => $x) {
			$visTmp += 2;
			$canConflict[$xi] = array_diff_key($nodes, $dependsOn[$xi]);
			$totalConflict[$xi] = array_diff_key($nodes, $canCooccur[$xi]);
		}
		$ts = (microtime(true) - $ts);
		$vis += $visTmp;
		$this->visitedCanTotalConflict = $visTmp;
		$this->timeCanTotalConflict = $ts;
		if ($this->debug) echo "Can conlict & total conflict: " . $ts . PHP_EOL;
		$ts = microtime(true);
		$visTmp = 0;
		foreach ($nodes as $xi => $x) {
			$visTmp++;
			$requires[$xi] = [];
			foreach ($canCooccur[$xi] as $yi => $yi) {
				$visTmp++;
				if ($xi !== $yi) {
					$visTmp += 2;
					// They can already co-occur
					if (!array_key_exists($yi, $canConflict[$xi]) && array_key_exists($xi, $canConflict[$yi])) {
						$requires[$xi][$yi] = $yi;
					}
				}
			}
		}
		$ts = (microtime(true) - $ts);
		$vis += $visTmp;
		$this->visitedRequires = $visTmp;
		$this->timeRequires = $ts;
		if ($this->debug) echo "Requires: " . $ts . PHP_EOL;
		$ts = microtime(true);
		$visTmp = 0;
		$flipped = [];
		$visTmp += count($nodes);
		foreach ($nodes as $xi => $x) $flipped[$xi] = [];
		foreach ($requires as $xi => $rel) {
			$visTmp++;
			foreach ($rel as $yi => $y) {
				$visTmp++;
				$flipped[$yi][$xi] = $x;
			}
		}
		foreach ($nodes as $xi => $x) {
			$visTmp += 4;
			$independent[$xi] = array_diff_key($nodes, $totalConflict[$xi], $totalCooccur[$xi], $requires[$xi], $flipped[$xi]);
		}
		$ts = (microtime(true) - $ts);
		$this->timeIndependent = $ts;
		$vis += $visTmp;
		if ($this->debug) echo "Independent: " . $ts . PHP_EOL;
		$this->visitedIndependent = $visTmp;
		$this->visitedNodes += $vis;
		
		// TODO: Check
		/*foreach ($nodes as $xi => $x) {
			$tmp = array_intersect_key($totalConflict[$xi], $totalCooccur[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, conflict<->cooccur : "; Util::printSet($tmp);
			}
			$tmp = array_intersect_key($totalConflict[$xi], $requires[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, conflict<->requires : "; Util::printSet($tmp);
			}
			$tmp = array_intersect_key($totalConflict[$xi], $independent[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, conflict<->independent : "; Util::printSet($tmp);
			}
			$tmp = array_intersect_key($requires[$xi], $totalCooccur[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, cooccur<->requires : "; Util::printSet($tmp);
			}
			$tmp = array_intersect_key($independent[$xi], $totalCooccur[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, cooccur<->independent : "; Util::printSet($tmp);
			}
			$tmp = array_intersect_key($requires[$xi], $independent[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, requires<->independent : "; Util::printSet($tmp);
			}
		}*/
		// TODO
		
		return [
			"can conflict" => $canConflict,
			"total conflict" => $totalConflict,
			"requires" => $requires,
			"independent" => $independent
		];
	}
	
	/**
	 * Compute the acyclic behavioral relations.
	 * @param Net @net The net.
	 * @return array
	 */
	public function computeAcyclicBehavioralRelations(Net $net) : array {
		$concurrency     = $this->compute($net);
		$causality       = $this->determineCausality($net);
		$canCooccur      = $this->determineCanCooccur($net, $concurrency, $causality);
		$activatingNodes = $this->determineActivatingNodes($net);
		$dependsOn       = $this->determineDependsOn($net, $activatingNodes);
		// TODO: Check
		/*foreach ($net->places + $net->transitions as $xi => $x) {
			$tmp = array_diff_key($dependsOn[$xi], $canCooccur[$xi]);
			if (count($tmp) > 0) {
				echo $xi . " has problems, dependson<->cancooccur : "; Util::printSet($tmp); Util::printSet($dependsOn[$xi]);
			}
		}*/
		// TODO
		$totalCooccur    = $this->determineTotalCooccurrence($net, $dependsOn);
		$others          = $this->determineOthers($net, $dependsOn, $canCooccur, $totalCooccur);
		return [
			"existential concurrency" => $concurrency,
			"total concurrency"       => $concurrency,
			"existential causality"   => $causality,
			"total causality"         => $causality,
			"can conflict"            => $others["can conflict"],
			"total conflict"          => $others["total conflict"],
			"can co-occur"            => $canCooccur,
			"total co-occur"          => $totalCooccur,
			"requires"                => $others["requires"],
			"independent"             => $others["independent"]
		];
	}
	
	
	
	
	
	/*
	 * Cyclic handling.
	 */
	
	private array $loopNets = [];
	private array $loopNodes = [];
	private array $virtualNodes = [];
	private int $netId = 1;
	private int $newIds = 1;
	private array $uniqueLoops = [];
	private int $numberNets = 0;
	
	public bool $dot = false;
	public string $file = '';
	
	/**
	 * Compute for cyclic.
	 */
	public function computeCyclic(Net $net) : array {
		$vis = 0;
		$net->id = 1;
		// Decompose the net
		$nets = $this->decomposeNet($net);
		$this->numberNets = count($nets);
		// Compute the relations for each net.
		$conc = [];
		foreach ($nets as $k => $net) $conc += $this->compute($net);
		$vis += count($nets);
		// Combine the information between the different nets.
		if (count($this->loopNodes) >= 1) {
			$remarkable = [];
			foreach ($this->loopNodes as $loopNode) $remarkable += $loopNode->remarkable;
			$vis += count($this->loopNodes);
			foreach ($remarkable as $pairId => $pair) {
				$vis++;
				unset($conc[$pairId]);
				$orgX = ($pair[0]->isLoopNode ? $this->loopNets[$pair[0]->id]->places : [ $pair[0] ]);
				$orgY = ($pair[1]->isLoopNode ? $this->loopNets[$pair[1]->id]->places : [ $pair[1] ]);
				foreach ($orgX as $x) {
					$vis++;
					if ($x->isVirtual) continue;
					foreach ($orgY as $y) {
						$vis++;
						if ($y->isVirtual) continue;
						$conc[$x->id . '-' . $y->id] = [$x,$y];
						$conc[$y->id . '-' . $x->id] = [$y,$x];
					}
				}
			}
		}		
		$this->visitedNodes += $vis;
		$this->visitedNodesAlgo += $vis;
		return $conc;
	}

	/**
	 * Recursively decompose the given net.
	 */
	private function decomposeNet(Net $net) : array {
		if ($this->debug) echo "Decompose net " . $net->id . PHP_EOL;
		$vis = 0;
		$loops = $this->detectLoops($net);
		if ($this->dot) file_put_contents($this->file . '_' . $net->id . '-' . $this->visitedNodes . '.dot', Util::toDot($net, $loops));
		if ($this->debug) echo "\tNet " . $net->id . " contains " . count($loops) . " loops" . PHP_EOL;
		if (count($loops) === 0) return [ $net ];
		
		$nets = $this->decomposeLoops($net, $loops);
		$subNets = [];
		foreach ($nets as $net) {
			$vis++;
			$subNets = array_merge($subNets, $this->decomposeNet($net));
		}
		$this->visitedNodes += $vis;
		$this->visitedNodesDecomposition += $vis;
		return $subNets;
	}

	/*
	 * Loop decomposition
	 */
	private function decomposeLoops(Net $net, array $loops) : array {
		$vis = 0;
		// Replace the loops with a place
		$nets = [$net->id => $net];
		
		foreach ($loops as $k => $loop) {
			$uniqueExit = $loop->exits[array_key_first($loop->exits)];
			if ($this->debug) echo "Loop " . $k . " of " . $net->id . PHP_EOL;
			$vis++;
			// Create a new net for the loop;
			if (!array_key_exists($uniqueExit->id, $this->uniqueLoops)) {
				$loopNet = new Net();
				$loopNet->id = $net->id . '_' . $uniqueExit->id;
				$nets[$loopNet->id] = $loopNet;
				$this->uniqueLoops[$uniqueExit->id] = $loopNet;
				
				// Copy the loop nodes
				$org = $loop->nodes + [];
				foreach ($loop->nodes as $node) {
					if ($node instanceof Place) {
						$copy = new Place();
					} else $copy = new Transition();
					$loop->nodes[$node->id] = $copy;
					if (array_key_exists($node->id, $loop->exits)) $loop->exits[$node->id] = $copy;
					if (array_key_exists($node->id, $loop->entries)) $loop->entries[$node->id] = $copy;
					$copy->id = $node->id;
					$copy->name = $node->name;
				}
			
				// Copy post- and presets
				foreach ($org as $n => $node) {
					$inLoop = array_intersect_key($node->preset, $loop->nodes);
					foreach ($inLoop as $k => $pre) $loop->nodes[$n]->preset[$k] = $loop->nodes[$k];
					$inLoop = array_intersect_key($node->postset, $loop->nodes);
					foreach ($inLoop as $k => $post) $loop->nodes[$n]->postset[$k] = $loop->nodes[$k];
				}
				
				// Determine transitions and places
				$loopNet->transitions = array_diff_key($loop->nodes, $net->places);
				$loopNet->places = array_diff_key($loop->nodes, $net->transitions);
			} else $loopNet = null;
			
			// Determine entries and exits in the net.
			if (count($loop->doBody) >= 1) {
				$realEntries = array_intersect_key($loop->exits, $loop->doBody);
			} else {
				$realEntries = $loop->entries;
			}
			$netRealEntries = array_intersect_key($net->places, $realEntries);
			$netExits = array_intersect_key($net->places, $loop->exits);
			
			// Remove all nodes not in the do-body (inclusive the "real" entries).
			$nonDoBody = array_diff_key($loop->nodes, $loop->doBody);
			if ($this->debug) { echo "Net-trans before: "; Util::printSet($net->transitions); }
			$net->transitions = array_diff_key($net->transitions, $nonDoBody);
			if ($this->debug) { echo "Net-trans after:  "; Util::printSet($net->transitions); }
			if ($this->debug) { echo "Net-places before: "; Util::printSet($net->places); }
			$net->places = array_diff_key($net->places, $nonDoBody + $realEntries);
			if ($this->debug) { echo "Net-places after:  "; Util::printSet($net->places); }
		
			// Insert a new loop node for the loop
			$loopNode = new Place();
			$loopNode->isLoopNode = true;
			$loopNode->id = "l_" . $net->id . '_' . $uniqueExit->id;
			$net->places[$loopNode->id] = $loopNode;
			$this->loopNets[$loopNode->id] = $this->uniqueLoops[$uniqueExit->id];
			$this->loopNodes[$loopNode->id] = $loopNode;
			$vis++;
			
			// We are not interested in the entries since they remain.
			// We are interested in exits of the do-body.
			if ($this->debug) { echo "Net real entries: "; Util::printSet($netRealEntries); }
			if ($this->debug) { echo "Net real exits: "; Util::printSet($netExits); }
			foreach ($netRealEntries as $entry) $loopNode->preset += array_diff_key($entry->preset, $nonDoBody);
			foreach ($netExits as $exit) $loopNode->postset += array_diff_key($exit->postset, $loop->nodes);
			$vis += count($realEntries) + count($loop->exits);
						
			// We have to update the predecessors and successors, respectively, of the loop entries and exits.
			foreach ($loopNode->preset as $pred) {
				$pred->postset = array_diff_key($pred->postset, $realEntries) + [$loopNode->id => $loopNode];
				$fId = "lf_" . $this->newIds++;
				$net->flows[$fId] = new Flow($fId, $pred, $loopNode);
			}
			foreach ($loopNode->postset as $succ) {
				$succ->preset = array_diff_key($succ->preset, $loop->exits) + [$loopNode->id => $loopNode];
				$fId = "lf_" . $this->newIds++;
				$net->flows[$fId] = new Flow($fId, $loopNode, $succ);
			}
			$vis += count($loopNode->preset) + count($loopNode->postset);
					
			// Now, update the flows
			foreach ($net->flows as $fId => $flow) {
				$vis++;
				$source = $flow->source; $target = $flow->target;
				
				// There are variants:
				$deleted = false;
				// 1. Parts of the flow are not in the net anymore: Remove from net.
				$srcExists = array_key_exists($source->id, $net->transitions + $net->places);
				$tgtExists = array_key_exists($target->id, $net->transitions + $net->places);
				if (!$srcExists || !$tgtExists) {
					if ($srcExists || $tgtExists) {
						if ($tgtExists) unset($target->preset[$source->id]);
						else unset($source->postset[$target->id]);
					}
					if ($this->debug) echo "Delete " . $flow->source->id . " -> " . $flow->target->id . PHP_EOL;
					unset($net->flows[$fId]);
					$deleted = true;
				}
				// 2. The flow is connected to the loop
				if ($loopNet && (array_key_exists($source->id, $loop->nodes) || array_key_exists($target->id, $loop->nodes))) {
					// a. The flow has a loop exit as target
					if (array_key_exists($target->id, $loop->exits)) {
						// Insert a new start place
						$lTarget = $loop->nodes[$target->id];
						$this->addStart($loopNet, $lTarget, $fId, $this->newIds);
						
						// Insert a new end place
						$lSource = $loop->nodes[$source->id];
						$this->addEnd($loopNet, $lSource, $fId, $this->newIds);						
						
						unset($lTarget->preset[$source->id]);
						unset($lSource->postset[$target->id]);
						
						if (array_key_exists($target->id, $realEntries) && (count($realEntries) === 1 || array_key_exists($source->id, $loop->doBody))) {
							$this->addStart($loopNet, $lTarget, $fId, $this->newIds);							
						}
						$vis += 2;
						
						// We do not need the flow in the loop net, so we do not add it.
					} else {
						// b. The flow is an inner flow, add it.
						if (array_key_exists($source->id, $loop->nodes) && array_key_exists($target->id, $loop->nodes)) {
							$loopNet->flows[$fId] = new Flow($fId, $loop->nodes[$source->id], $loop->nodes[$target->id]);
						}
					}					
				}
			}
			
			if ($this->debug && $loopNet) {
				echo "Check " . $loopNet->id . ": " . PHP_EOL;
				var_dump(Util::checkNet($loopNet));
			}
		}	 
		$this->visitedNodes += $vis;
		$this->visitedNodesDecomposition += $vis;
		/*if ($this->dot) {
			foreach ($nets as $n) file_put_contents($this->file . '_' . $n->id . '.dot', Util::toDot($n));
		}*/
		if ($this->debug) {
			echo "Check " . $net->id . ": " . PHP_EOL;
			var_dump(Util::checkNet($net));
		}
		/*var_dump(array_map(function (Flow $flow) {
			return $flow->source->id . " -> " . $flow->target->id;
		}, $net->flows));*/
		return $nets;
	}
	
	/**
	 * Add a start place with a transition to the given target.
	 */
	private function addStart(Net $net, Node $target, string $fId, int &$i) : void {
		$startTrans = new Transition();
		$startTrans->id = $fId . "_" . $i++;
		$startTrans->postset[$target->id] = $target;
		$target->preset[$startTrans->id] = $startTrans;
		$startTrans->isVirtual = true;
		$this->virtualNodes[$startTrans->id] = $startTrans;
		
		$startPlace = new Place();
		$startPlace->id = $fId . "_" . $i++;
		$startPlace->postset[$startTrans->id] = $startTrans;
		$startTrans->preset[$startPlace->id] = $startPlace;
		$startPlace->isVirtual = true;
		$this->virtualNodes[$startPlace->id] = $startPlace;
		
		$net->flows['se' . $i] = new Flow('se' . $i++, $startTrans, $target);
		$net->flows['se' . $i] = new Flow('se' . $i++, $startPlace, $startTrans);
		$net->places[$startPlace->id] = $startPlace;
		$net->transitions[$startTrans->id] = $startTrans;
		$net->starts[$startPlace->id] = $startPlace;
		$this->visitedNodes += 3;
		$this->visitedNodesDecomposition += 3;
	}
	
	/**
	 * Add an end place with a transition from the given source.
	 */
	private function addEnd(Net $net, Node $source, string $fId, int &$i) : void {
		$endTrans = new Transition();
		$endTrans->id = $fId . "_" . $i++;
		$endTrans->preset[$source->id] = $source;
		$source->postset[$endTrans->id] = $endTrans;
		$endTrans->isVirtual = true;
		$this->virtualNodes[$endTrans->id] = $endTrans;
		
		$endPlace = new Place();
		$endPlace->id = $fId . "_" . $i++;
		$endPlace->preset[$endTrans->id] = $endTrans;
		$endTrans->postset[$endPlace->id] = $endPlace;
		$endPlace->isVirtual = true;
		$this->virtualNodes[$endPlace->id] = $endPlace;
		
		$net->flows['ee' . $i] = new Flow('ee' . $i++, $source, $endTrans);
		$net->flows['ee' . $i] = new Flow('ee' . $i++, $endTrans, $endPlace);
		$net->places[$endPlace->id] = $endPlace;
		$net->transitions[$endTrans->id] = $endTrans;
		$net->ends[$endPlace->id] = $endPlace;
		
		$this->visitedNodes += 3;
		$this->visitedNodesDecomposition += 3;
	}



	/*
	 * Loop detection
	 */

	private array $components = [];		
	private int $index = 0;	
	private array $unindexed = [];	
	private array $stack = [];	
	private array $tmpNodes = [];

	/**
	 * Detect loops in a given net by Tarjan's algorithm.
	 */
	public function detectLoops(Net $net) : array {
		$vis = 1;
		$this->components = [];
		$this->stack = [];
		
		$this->unindexed = $net->places + $net->transitions;
		$this->tmpNodes = $net->places + $net->transitions;
		while (count($this->unindexed) > 0) {
			$vis++;
			$this->strongConnect(array_shift($this->unindexed));
		}
		$this->determineLoopBodies($net, $this->components);
		$this->visitedNodes += $vis;
		$this->visitedNodesDetection += $vis;
		return array_merge([], $this->components);
	}

	/**
	 * Part of detectLoops.
	 */
	private function strongConnect(Node $node) : void {
		$vis = 1;
		$node->index = $this->index;
		unset($this->unindexed[$node->id]);
		$node->lowlink = $this->index++;

		$this->stack[] = $node->id;

		foreach ($node->postset as $s) {
			if (array_key_exists($s->id, $this->unindexed)) {
				$this->strongConnect($s);
				$node->lowlink = min($node->lowlink, $s->lowlink);
			} else if (in_array($s->id, $this->stack, true)) {
				$node->lowlink = min($node->lowlink, $s->index);
			}
		}
		$vis += count($node->postset);
		
		if ($node->lowlink === $node->index) {
			$comp = new Loop();
			$preset = [];
			$postset = [];
			do {
				$vis++;
				$current = array_pop($this->stack);
				$currentNode = $this->tmpNodes[$current];
				$comp->nodes[$current] = $currentNode;
				$preset += $currentNode->preset;
				$postset += $currentNode->postset;
			} while ($current !== $node->id);
			
			if (count($comp->nodes) > 1) {
				// Determine entries and exits
				$preset = array_diff_key($preset, $comp->nodes);
				$postset = array_diff_key($postset, $comp->nodes);
				foreach ($preset as $in) $comp->entries += array_intersect_key($in->postset, $comp->nodes);
				foreach ($postset as $out) $comp->exits += array_intersect_key($out->preset, $comp->nodes);
				$vis += count($preset) + count($postset);
				
				ksort($comp->exits);
				
				$this->components[] = $comp;
			}
			
		}
		$this->visitedNodes += $vis;
		$this->visitedNodesDetection += $vis;
	}
	
	/**
	 * Determines the do-bodies of the loops.
	 */
	private function determineLoopBodies(Net $net, array $loops) : void {
		$vis = 1;
		foreach ($loops as $loop) {
			$vis++;
			if (count($loop->entries) === 1) {
				// We do not have to determine the do-body.
				$loop->doBody = [];
				continue;
			}
			// Determine do-body
			$workingList = $loop->entries + [];
            $doBody = $workingList + [];
			$cut = [];
			foreach ($loop->exits as $exit) $cut += $exit->postset;
			$vis += count($loop->exits);
            while (count($workingList) > 0) {
				$vis++;
                $cur = array_shift($workingList);
				$next = array_intersect_key(array_diff_key($cur->postset, $cut + $doBody), $loop->nodes);
					$doBody += $next;
				$workingList += $next;
            }
			$loop->doBody = $doBody;
		}
		$this->visitedNodes += $vis;
		$this->visitedNodesDecomposition += $vis;
	}
	
	public function generateDotOut(bool $dot) : void {
		$this->dot = $dot;
	}
	
	public function getVisitedNodes() : int {
		return $this->visitedNodes;
	}
	
	public function getNumberLoops() : int {
		return count($this->uniqueLoops);
	}
	
	public function getNumberInvestigatedNets() : int {
		return $this->numberNets;
	}
}
?>