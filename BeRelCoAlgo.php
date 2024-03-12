<?php
include_once "Algo.php";

/**
 * Class BeRelCoAlgo.
 *
 * Implementation of the BeRelCo algorithms.
 */
class BeRelCoAlgo implements Algo {

    /**
     * Debug.
     * @var bool
     */
	private bool $debug = false;
    /**
     * Validation of the results.
     * @var bool
     */
    private bool $validation = false;

    /**
     * Different computation times for the different algorithms.
     * @var string
     */
	public string $timeExistConcurrency;
	public string $timeExistCausality;
	public string $timeCanCoOccur;
	public string $timeTriggers;
	public string $timeCannotConflict;
	public string $timeTotalCoOccurrence;
	public string $timeCanTotalConflict;
	public string $timeRequires;
	public string $timeIndependent;

    /**
     * Total number of visited nodes in the different algorithms.
     * @var int
     */
    private int $visitedNodes = 0;
    public int $visitedNodesHasPath = 0;
	public int $visitedExistConcurrency = 0;
	public int $visitedExistCausality = 0;
	public int $visitedCanCoOccur = 0;
	public int $visitedTriggers = 0;
	public int $visitedCannotConflict = 0;
	public int $visitedTotalCoOccurrence = 0;
	public int $visitedCanTotalConflict = 0;
	public int $visitedRequires = 0;
	public int $visitedIndependent = 0;

	/**
	 * Concurrent paths (CP) algorithm.
     *
     * <cite>
     * Prinz, T.M., Klaus, J., van Beest, N.R.T.P.: Pushing the limits: Concurrency detection in
     * acyclic, live, and 1-safe free-choice nets in O((P + T)^2). CoRR abs/2401.16097 (2024).
     * https://doi.org/10.48550/ARXIV.2401.16097
     * </cite>
     *
	 * @param Net $net The net.
	 * @return array
	 */
	public function existentialConcurrency(Net $net) : array {
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
					$hasPathsX = array_diff_key($x->reaches, $y->reaches);
					foreach ($hasPathsX as $sX) {
						$vis++;
						$P[$sX->id] = $sX;
						$hasPathsXY = array_diff_key($y->reaches, $sX->reaches);
						$P[$sX->id]->parallel += $hasPathsXY;
					}
				}
			}
		}
		$R = [];
		$vis += count($nodes);
		foreach ($nodes as $xi => $x) $R[$xi] = [];
		foreach ($nodes as $xi => $x) {
			$vis++;
			$R[$xi] += $x->parallel;
			$vis += count($x->parallel);
			foreach ($x->parallel as $yi => $y) $R[$yi][$xi] = $x; 
		}
		$ts = (microtime(true) - $ts);
		$this->timeExistConcurrency = $ts;
		if ($this->debug) echo "Concurrency: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedExistConcurrency += $vis;
		return $R;
	}

	/**
	 * Determine all nodes a node has a path to.
	 * @param Net $net The net.
	 * @return void
	 */
	private function determineHasPath(Net $net) : void {
		if ($this->debug) $ts = microtime(true);
		$vis = 0;
		$visited = [];
		$current = $net->ends + [];
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
				$cur->reaches[$cur->id] = $cur;
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
	private function determineCanCoOccur(Net $net, array $concurrency, array $causality) : array {
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
				$flipped[$yi][$xi] = $nodes[$xi];
			}
		}
		foreach ($nodes as $xi => $x) {
			$vis++;
			$R[$xi] = $concurrency[$xi] + $causality[$xi] + $flipped[$xi];
		}
		$ts = (microtime(true) - $ts);
		$this->timeCanCoOccur = $ts;
		if ($this->debug) echo "Can co-occur: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedCanCoOccur = $vis;
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
		$this->visitedTriggers += $vis;
		return $L;
	}

	/**
	 * Orders the nodes of the net reverse topologically.
	 * @param Net $net The net.
	 * @return array
	 */
	private function reverseTopologicalSort(Net $net) : array {
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
		$this->visitedCannotConflict += $vis;
		return $L;
	}
	
	/**
	 * Determines the triggers relation.
	 * @param Net $net The net.
	 * @return array
	 */
	private function determineTriggers(Net $net) : array {
		$ts = microtime(true);
		$vis = 0;
		$R = [];
		$L = $this->reverseTopologicalSort($net);
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
		$this->timeTriggers = $ts;
		if ($this->debug) echo "Triggers: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedTriggers += $vis;
		return $R;
	}
	
	/**
	 * Compute the cannot-conflict relation.
	 * @param Net $net The net.
	 * @param array $triggers The triggers relation as adjacency list.
	 * @return array
	 */
	private function determineCannotConflict(Net $net, array $triggers) : array {
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
			$tmpR += $triggers[$x->id];
			$R[$x->id] = $tmpR;
		}
		foreach ($R as $xi => $list) {
			$vis++;
			unset($list[$xi]);
			$R[$xi] = $list;
		}
		$ts = (microtime(true) - $ts);
		$this->timeCannotConflict = $ts;
		if ($this->debug) echo "Cannot conflict: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedCannotConflict += $vis;
		return $R;		
	}
	
	/**
	 * Compute the total-occurrence relation.
	 * @param Net $net The net.
	 * @param array $cannotConflict The cannot-conflict relation as adjacency list.
	 * @return array
	 */
	private function determineTotalCoOccurrence(Net $net, array $cannotConflict) : array  {
		$ts = microtime(true);
		$vis = 0;
		$R = [];
		$nodes = $net->places + $net->transitions;
		foreach ($nodes as $xi => $x) {
			$vis++;
			$R[$xi] = [];
			$M = $cannotConflict[$xi];
			foreach ($M as $yi => $y) {
				$vis++;
				if (array_key_exists($xi, $cannotConflict[$yi])) {
					$R[$xi][$yi] = $y;
				}
			}
		}
		$ts = (microtime(true) - $ts);
		$this->timeTotalCoOccurrence = $ts;
		if ($this->debug) echo "Total Co-occurrence: " . $ts . PHP_EOL;
		$this->visitedNodes += $vis;
		$this->visitedTotalCoOccurrence = $vis;
		return $R;
	}
	
	/**
	 * Compute the missing relations.
	 * @param Net $net The net.
	 * @param array $cannotConflict The cannot-conflict relation.
	 * @param array $canCoOccur The can-co-occur relation.
	 * @param array $totalCoOccur The total co-occurrence relation.
	 * @return array
	 */
	private function determineOthers(Net $net, array $cannotConflict, array $canCoOccur, array $totalCoOccur) : array {
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
			$canConflict[$xi] = array_diff_key($nodes, $cannotConflict[$xi]);
			$totalConflict[$xi] = array_diff_key($nodes, $canCoOccur[$xi]);
		}
		$ts = (microtime(true) - $ts);
		$vis += $visTmp;
		$this->visitedCanTotalConflict = $visTmp;
		$this->timeCanTotalConflict = $ts;
		if ($this->debug) echo "Can conflict & total conflict: " . $ts . PHP_EOL;
		$ts = microtime(true);
		$visTmp = 0;
		foreach ($nodes as $xi => $x) {
			$visTmp++;
			$requires[$xi] = [];
			foreach ($canCoOccur[$xi] as $yi => $y) {
				$visTmp++;
				if ($xi !== $yi) {
					$visTmp += 2;
					// They can already co-occur
					if (!array_key_exists($yi, $canConflict[$xi]) && array_key_exists($xi, $canConflict[$yi])) {
						$requires[$xi][$yi] = $y;
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
			$independent[$xi] = array_diff_key($nodes, $totalConflict[$xi], $totalCoOccur[$xi], $requires[$xi], $flipped[$xi]);
		}
		$ts = (microtime(true) - $ts);
		$this->timeIndependent = $ts;
		$vis += $visTmp;
		if ($this->debug) echo "Independent: " . $ts . PHP_EOL;
		$this->visitedIndependent = $visTmp;
		$this->visitedNodes += $vis;
		
		if ($this->validation) {
            foreach ($nodes as $xi => $x) {
                $tmp = array_intersect_key($totalConflict[$xi], $totalCoOccur[$xi]);
                if (count($tmp) > 0) {
                    echo $xi . " has problems, conflict<->cooccur : ";
                    Util::printSet($tmp);
                }
                $tmp = array_intersect_key($totalConflict[$xi], $requires[$xi]);
                if (count($tmp) > 0) {
                    echo $xi . " has problems, conflict<->requires : ";
                    Util::printSet($tmp);
                }
                $tmp = array_intersect_key($totalConflict[$xi], $independent[$xi]);
                if (count($tmp) > 0) {
                    echo $xi . " has problems, conflict<->independent : ";
                    Util::printSet($tmp);
                }
                $tmp = array_intersect_key($requires[$xi], $totalCoOccur[$xi]);
                if (count($tmp) > 0) {
                    echo $xi . " has problems, cooccur<->requires : ";
                    Util::printSet($tmp);
                }
                $tmp = array_intersect_key($independent[$xi], $totalCoOccur[$xi]);
                if (count($tmp) > 0) {
                    echo $xi . " has problems, cooccur<->independent : ";
                    Util::printSet($tmp);
                }
                $tmp = array_intersect_key($requires[$xi], $independent[$xi]);
                if (count($tmp) > 0) {
                    echo $xi . " has problems, requires<->independent : ";
                    Util::printSet($tmp);
                }
            }
        }
		
		return [
			"can conflict" => $canConflict,
			"total conflict" => $totalConflict,
			"requires" => $requires,
			"independent" => $independent
		];
	}
	
	/**
	 * Compute the acyclic behavioral relations.
	 * @param Net $net The net.
	 * @return array
	 */
	public function computeAcyclicBehavioralRelations(Net $net) : array {
		$concurrency     = $this->existentialConcurrency($net);
		$causality       = $this->determineCausality($net);
		$canCoOccur      = $this->determineCanCoOccur($net, $concurrency, $causality);
		$triggers        = $this->determineTriggers($net);
		$cannotConflict  = $this->determineCannotConflict($net, $triggers);
		$totalCoOccur    = $this->determineTotalCoOccurrence($net, $cannotConflict);
		$others          = $this->determineOthers($net, $cannotConflict, $canCoOccur, $totalCoOccur);
		return [
			"existential concurrency" => $concurrency,
			"total concurrency"       => $concurrency,
			"existential causality"   => $causality,
			"total causality"         => $causality,
			"can conflict"            => $others["can conflict"],
			"total conflict"          => $others["total conflict"],
			"can co-occur"            => $canCoOccur,
			"total co-occur"          => $totalCoOccur,
			"requires"                => $others["requires"],
			"independent"             => $others["independent"]
		];
	}
	
	public function getVisitedNodes() : int {
		return $this->visitedNodes;
	}
}
?>