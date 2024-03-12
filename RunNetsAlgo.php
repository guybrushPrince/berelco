<?php
include_once "Algo.php";
include_once "RunNet.php";

/**
 * Class RunNetAlgo.
 *
 * Implementation of a run net derivation algorithm.
 */
class RunNetsAlgo implements Algo {

    /**
     * The number of maximal instances.
     */
	const MAX_NUMBER_INSTANCES = 500000;

    /**
     * The number of visited nodes.
     * @var int
     */
	private int $visitedNodes = 0;

    /**
     * The number of visited nodes during has-path.
     * @var int
     */
	public int $visitedNodesHasPath = 0;

    /**
     * The overall number of run nets.
     * @var int
     */
	public int $numberRunNets = 0;
	
	/**
	 * Derive all run nets of an acyclic net.
	 * @param Net $net The net.
	 * @return RunNet[]
	 */
	private function deriveRunNets(Net $net) : array {
		$vis = 0;
		$runNets = [];
		$finished = [];
		$starts = $net->starts;
		foreach ($starts as $si => $start) {
			$vis++;
			$runNet = new RunNet($net, [ $si => $start ]);
			$runNets[$runNet->id] = $runNet;
		}
		while (count($runNets) > 0) {
			$vis++;
			if (count($runNets) > self::MAX_NUMBER_INSTANCES) return []; // TODO
			foreach ($runNets as $runNet) {
				$vis++;
				$nRunNets = $runNet->step();
				$vis += $runNet->visitedNodes;
				unset($runNets[$runNet->id]);
				if (count($nRunNets) > 0) {
					$runNets += $nRunNets;
				} else {
					$finished[] = $runNet;
				}
			}
		}
		$this->visitedNodes += $vis;
		$this->numberRunNets = count($finished);

		return $finished;
	}

    /**
     * Compute the behavioral relations based on run nets.
     * @param Net $net The net.
     * @return array
     */
	public function compute(Net $net) : array {
		$net = $this->repair($net);
		$this->determineHasPath($net);
		$this->visitedNodes += $this->visitedNodesHasPath;
		$runNets = $this->deriveRunNets($net);
		if (count($runNets) > 0) {
			$canCoOccur = $this->computeCanCoOccur($net, $runNets);
			$canConflict = $this->computeCanConflict($net, $runNets);
			$causality = $this->computeCausal($net, $canCoOccur);
			$concurrency = $this->computeConcurrency($net, $canCoOccur, $causality);
			$others = $this->computeOthers($net, $canCoOccur, $canConflict);
			
			return array_merge([
				"existential concurrency" => $concurrency,
				"total concurrency"       => $concurrency,
				"existential causality"   => $causality,
				"total causality"         => $causality,
				"can conflict"            => $canConflict,
				"can co-occur"            => $canCoOccur
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

    /**
     * Compute the can-co-occur relation.
     * @param Net $net The net ...
     * @param RunNet[] $runNets ... and its run nets.
     * @return array
     */
	private function computeCanCoOccur(Net $net, array $runNets) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$R = [];
		foreach ($nodes as $xi => $x) {
			$vis += 2 * count($runNets) + 1;
			$appear = array_filter($runNets, function(RunNet $runNet) use ($xi) {
				return array_key_exists($xi, $runNet->getContains());
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

    /**
     * Compute the can-conflict relation.
     * @param Net $net The net ...
     * @param RunNet[] $runNets ... and its run nets.
     * @return array
     */
	private function computeCanConflict(Net $net, array $runNets) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$R = [];
		foreach ($nodes as $xi => $x) {
			$vis += 2 * count($runNets) + 2;
			$appear = array_filter($runNets, function(RunNet $runNet) use ($xi) {
				return array_key_exists($xi, $runNet->getContains());
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

    /**
     * Compute the causality relation.
     * This is a non-naive implementation, which considers can-co-occur and has-paths.
     * @param Net $net The net.
     * @param array $canCoOccur The can co-occur relation.
     * @return array
     */
	private function computeCausal(Net $net, array $canCoOccur) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$R = [];
		$vis += count($nodes);
		foreach ($nodes as $xi => $x) {
			$R[$xi] = array_intersect_key($canCoOccur[$xi], $x->reachesIns);
		}
		$this->visitedNodes += $vis;
		return $R;
	}

    /**
     * Compute the concurrency relation.
     * This is a non-naive implementation, which derives the concurrency relation from the can-co-occur and causality
     * relations.
     * @param Net $net The net.
     * @param array $canCoOccur The can-co-occur relation.
     * @param array $causality The causality relation.
     * @return array
     */
	private function computeConcurrency(Net $net, array $canCoOccur, array $causality) : array {
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
			$R[$xi] = array_diff_key($canCoOccur[$xi], $causality[$xi], $flipped[$xi]);
		}
		$this->visitedNodes += $vis;
		return $R;
	}

    /**
     * Compute the other relations.
     * @param Net $net The net.
     * @param array $canCoOccur The can-co-occur relation.
     * @param array $canConflict The can-conflict relation.
     * @return array[]
     */
	private function computeOthers(Net $net, array $canCoOccur, array $canConflict) : array {
		$vis = 0;
		$nodes = $net->places + $net->transitions;
		$totalConflict = [];
		$requires = [];
		$independent = [];
		$totalCoOccur = [];
		foreach ($nodes as $xi => $x) {
			$vis += 3;
			$totalConflict[$xi] = array_diff_key($nodes, $canCoOccur[$xi]);
			$totalCoOccur[$xi] = [];
			$requires[$xi] = [];
			$independent[$xi] = [];
			foreach ($nodes as $yi => $y) {
				$vis++;
				if (array_key_exists($yi, $canCoOccur[$xi])) {
					$vis += 6;
					if (!array_key_exists($xi, $canConflict[$yi]) && !(array_key_exists($yi, $canConflict[$xi]))) {
						$totalCoOccur[$xi][$yi] = $y;
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
			"total co-occur"          => $totalCoOccur,
			"requires"                => $requires,
			"independent"             => $independent
		];
	}

    /**
     * Determine all nodes a node has a path to.
     * @param Net $net The net.
     * @return void
     */
	private function determineHasPath(Net $net) : void {
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
				foreach ($cur->postset as $p) $cur->reachesIns += $p->reachesIns;
				$vis += count($cur->postset);
				$cur->reachesIns[$cur->id] = $cur;
				$current = $current + $cur->preset;
			}
		} while (count($current) > 0);
		$this->visitedNodes += $vis;
		$this->visitedNodesHasPath += $vis;
	}

    /**
     * Get the number of visited nodes.
     * @return int
     */
	public function getVisitedNodes() : int {
		return $this->visitedNodes;
	}

    /**
     * Repairs a net if it has a start/end node being a transition.
     * @param Net $net The net.
     * @return Net
     */
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
     * @param Net $net The net.
     * @param Node $target The target.
     * @return void
     */
	private function addStart(Net $net, Node $target) : void {
		$startPlace = new Place();
		$startPlace->id = "pv" . $target->id;
		$startPlace->postset[$target->id] = $target;
		$target->preset[$startPlace->id] = $startPlace;
		$startPlace->isVirtual = true;
		
		$net->flows['vi' . $target->id] = new Flow('vi' . $target->id, $startPlace, $target);
		$net->places[$startPlace->id] = $startPlace;
		$net->starts[$startPlace->id] = $startPlace;
		unset($net->starts[$target->id]);
		$this->visitedNodes += 2;
	}
	
	/**
	 * Add an end place with a transition from the given source.
     * @param Net $net The net.
     * @param Node $source The source.
     * @return void
     */
	private function addEnd(Net $net, Node $source) : void {
		$endPlace = new Place();
		$endPlace->id = "pv" . $source->id;
		$endPlace->preset[$source->id] = $source;
		$source->postset[$endPlace->id] = $endPlace;
		$endPlace->isVirtual = true;
		
		$net->flows['vi' . $source->id] = new Flow('vi' . $source->id, $source, $endPlace);
		$net->places[$endPlace->id] = $endPlace;
		$net->ends[$endPlace->id] = $endPlace;
		unset($net->ends[$source->id]);
		
		$this->visitedNodes += 2;
	}
}
?>