<?php
include_once "Algo.php";
include_once "Instance.php";

class InstanceAlgo implements Algo {
	
	private int $visitedNodes = 0;
	public int $visitedNodesHasPath = 0;
	private array $virtualNodes = [];
	public int $numberInstances = 0;
	
	/**
	 * Derive all instances of an acyclic net.
	 * @param Net $net The net.
	 * @return Instance[]
	 */
	private function deriveInstances(Net $net) : array {
		$vis = 0;
		$instances = [];
		$finished = [];
		$starts = $net->starts;
		foreach ($starts as $si => $start) {
			$vis++;
			$instance = new Instance($net, [ $si => $start ]);
			$instances[$instance->id] = $instance;
		}
		while (count($instances) > 0) {
			$vis++;
			if (count($instances) > 100000) return []; // TODO
			foreach ($instances as $instance) {
				$vis++;
				$nInstances = $instance->step();
				$vis += $instance->visitedNodes;
				unset($instances[$instance->id]);
				if (count($nInstances) > 0) {					
					$instances += $nInstances;
				} else {
					$finished[] = $instance;
				}
			}
		}
		$this->visitedNodes += $vis;
		$this->numberInstances = count($finished);
		// Check
		/*foreach ($finished as $instance) {
			$final = array_diff_key($instance->withTokens, $net->ends);
			if (count($final) > 0) {
				echo "Unfinished instance: " . $instance->out() . PHP_EOL;
				foreach ($final as $f) var_dump([
					"class" => get_class($f),
					"id" => $f->id,
					"OR" => $f->simulatesOR ? "TRUE" : "FALSE",
					"postset" => array_map(function (Node $n) {
						return [
							"class" => get_class($n),
							"id" => $n->id,
							"OR" => $n->simulatesOR ? "TRUE" : "FALSE",
						];
					}, $f->postset)
				]);
			}
		}*/
		// End Check
		return $finished;
	}
	
	public function compute(Net $net) : array {
		$net = $this->repair($net);
		$this->determineHasPath($net);
		$this->visitedNodes += $this->visitedNodesHasPath;
		$instances = $this->deriveInstances($net);
		if (count($instances) > 0) {
			$canCooccur = $this->computeCanCooccur($net, $instances);
			$canConflict = $this->computeCanConflict($net, $instances);
			$causality = $this->computeCausal($net, $canCooccur);
			$concurrency = $this->computeConcurrency($net, $canCooccur, $causality);
			$others = $this->computeOthers($net, $canCooccur, $canConflict);
			
			//foreach ($instances as $instance) echo $instance->out() . PHP_EOL;
			//Util::printSet($canCooccur);
			
			return array_merge([
				"existential concurrency" => $concurrency,
				"total concurrency"       => $concurrency,
				"existential causality"   => $causality,
				"total causality"         => $causality,
				"can conflict"            => $canConflict,
				"can co-occur"            => $canCooccur
			], $others);
		} else {
			echo "\tIntractable" . PHP_EOL;
			return [
				"existential concurrency" => [],
				"total concurrency"       => [],
				"existential causality"   => [],
				"total causality"         => [],
				"can conflict"            => [],
				"can co-occur"            => [],
				"total conflict"          => [],
				"total co-occur"          => [],
				"requires"                => [],
				"independent"             => [],
				"intractable"			  => true
			];
		}
	}
	
	
	
	private function computeCanCooccur(Net $net, array $instances) {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$R = [];
		foreach ($nodes as $xi => $x) {
			$vis += 2 * count($instances) + 1;
			$appear = array_filter($instances, function(Instance $instance) use ($xi) {
				return array_key_exists($xi, $instance->getContains());
			});
			$R[$xi] = [];
			foreach ($appear as $ins) {
				$R[$xi] += $ins->getContains();
			}
			unset($R[$xi][$xi]);
		}
		$this->visitedNodes += $vis;
		return $R;
	}
	
	private function computeCanConflict(Net $net, array $instances) {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$R = [];
		foreach ($nodes as $xi => $x) {
			$vis += 2 * count($instances) + 2;
			$appear = array_filter($instances, function(Instance $instance) use ($xi) {
				return array_key_exists($xi, $instance->getContains());
			});
			$R[$xi] = [];
			foreach ($appear as $ins) {
				$R[$xi] += array_diff_key($nodes, $ins->getContains());
			}
			$R[$xi][$xi] = $x;
		}
		$this->visitedNodes += $vis;
		return $R;
	}
	
	private function computeCausal(Net $net, array $canCooccur) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$R = [];
		$vis += count($nodes);
		foreach ($nodes as $xi => $x) {
			$R[$xi] = array_intersect_key($canCooccur[$xi], $x->reachesIns);
		}
		$this->visitedNodes += $vis;
		return $R;
	}
	
	private function computeConcurrency(Net $net, array $canCooccur, array $causality) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$flipped = [];
		$vis += count($nodes);
		foreach ($nodes as $xi => $x) $flipped[$xi] = [];
		foreach ($causality as $xi => $rel) {
			$vis += count($rel) + 1;
			foreach ($rel as $yi => $y) {
				$flipped[$yi][$xi] = $x;
			}
		}
		$R = [];
		$vis += count($nodes) * 2;
		foreach ($nodes as $xi => $x) {
			$R[$xi] = array_diff_key($canCooccur[$xi], $causality[$xi], $flipped[$xi]);
		}
		$this->visitedNodes += $vis;
		return $R;
	}
	
	private function computeOthers(Net $net, array $canCooccur, array $canConflict) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$totalConflict = [];
		$requires = [];
		$independent = [];
		$totalCooccur = [];
		foreach ($nodes as $xi => $x) {
			$vis += 3;
			$totalConflict[$xi] = array_diff_key($nodes, $canCooccur[$xi]);
			$totalCooccur[$xi] = [];
			$requires[$xi] = [];
			$independent[$xi] = [];
			foreach ($nodes as $yi => $y) {
				$vis++;
				if (array_key_exists($yi, $canCooccur[$xi])) {
					$vis += 6;
					if (!array_key_exists($xi, $canConflict[$yi]) && !(array_key_exists($yi, $canConflict[$xi]))) {
						$totalCooccur[$xi][$yi] = $y;
					}
					if (array_key_exists($xi, $canConflict[$yi]) && !(array_key_exists($yi, $canConflict[$xi]))) {
						$requires[$xi][$yi] = $y;
					}
					if (array_key_exists($xi, $canConflict[$yi]) && array_key_exists($yi, $canConflict[$xi])) {
						$independent[$xi][$yi] = $y;
					}
				}
			}
		}
		$this->visitedNodes += $vis;
		return [
			"total conflict"          => $totalConflict,
			"total co-occur"          => $totalCooccur,
			"requires"                => $requires,
			"independent"             => $independent
		];
	}
	
	/**
	 * New algorithm: Determine all nodes a node has a path to.
	 */
	private function determineHasPath(Net $net) : void {
		//if ($this->debug) $ts = microtime(true);
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
				foreach ($cur->postset as $p) $cur->reachesIns += $p->reachesIns;
				$vis += count($cur->postset);
				$cur->reachesIns[$cur->id] = $cur;
				$current = $current + $cur->preset;
			}
		} while (count($current) > 0);
		$this->visitedNodes += $vis;
		$this->visitedNodesHasPath += $vis;
		//if ($this->debug) echo "HasPath: " . (microtime(true) - $ts) . PHP_EOL;
	}
	
	
	
	
	public function getVisitedNodes() : int {
		return $this->visitedNodes;
	}
	
	private function repair(Net $net) : Net {
		foreach ($net->starts as $start) {
			if ($start instanceof Transition) {
				$this->addStart($net, $start);
			}
		}
		foreach ($net->ends as $end) {
			if ($end instanceof Transition) {
				$this->addEnd($net, $end);
			}
		}
		return $net;
	}
	
	/**
	 * Add a start place with a transition to the given target.
	 */
	private function addStart(Net $net, Node $target) : void {
		$startPlace = new Place();
		$startPlace->id = "pv" . $target->id;
		$startPlace->postset[$target->id] = $target;
		$target->preset[$startPlace->id] = $startPlace;
		$startPlace->isVirtual = true;
		$this->virtualNodes[$startPlace->id] = $startPlace;
		
		$net->flows['vi' . $target->id] = new Flow('vi' . $target->id, $startPlace, $target);
		$net->places[$startPlace->id] = $startPlace;
		$net->starts[$startPlace->id] = $startPlace;
		unset($net->starts[$target->id]);
		$this->visitedNodes += 2;
	}
	
	/**
	 * Add an end place with a transition from the given source.
	 */
	private function addEnd(Net $net, Node $source) : void {
		$endPlace = new Place();
		$endPlace->id = "pv" . $source->id;
		$endPlace->preset[$source->id] = $source;
		$source->postset[$endPlace->id] = $endPlace;
		$endPlace->isVirtual = true;
		$this->virtualNodes[$endPlace->id] = $endPlace;
		
		$net->flows['vi' . $source->id] = new Flow('vi' . $source->id, $source, $endPlace);
		$net->places[$endPlace->id] = $endPlace;
		$net->ends[$endPlace->id] = $endPlace;
		unset($net->ends[$source->id]);
		
		$this->visitedNodes += 2;
	}

}
?>