<?php
class RunNet {
	
	public int $visitedNodes = 0;
	
	public static int $counter = 0;
	public int $id;

	public array $executed = [];
	public array $withTokens = [];
	public Net $net;
	
	public function __construct(Net $net, array $withTokens, array $init = []) {
		$this->id = self::$counter++;
		$this->net = $net;
		$this->executed = array_merge($this->executed, $init);
		$this->withTokens = $withTokens;
		$this->visitedNodes++;
	}
	
	public function step() : array {
		$vis = 0;
		$enabled = array_reduce($this->withTokens, function (array $enabled, Place $place) use (&$vis) {
			$vis++;
			foreach ($place->postset as $ti => $t) {
				$vis += 2;
				$checkOR = count($t->preset) >= 2 && $t->simulatesOR;
				if (!$checkOR) {
					$tmp = array_diff_key($t->preset, $this->withTokens);
					if (count($tmp) === 0) {
						$enabled[$ti] = $t;
					}
				} else { // OR-join semantics
					$vis += 2;
					$tmp = array_intersect_key($t->preset, $this->withTokens);
					$tmp2 = array_diff_key($this->withTokens, $t->preset);
					if (count($tmp) > 0) {
						$en = true;
						foreach ($tmp2 as $pi => $p) {
							if (array_key_exists($ti, $p->reachesIns)) {
								$en = false;
								break;
							}
						}
						if ($en) $enabled[$ti] = $t;
					}
				}
			}
			return $enabled;
		}, []);
		/*echo $this->id . " With tokens: ";
		Util::printSet($this->withTokens);
		echo $this->id . " Enabled: ";
		Util::printSet($enabled);*/
		//echo $this->out() . PHP_EOL;
		if (count($enabled) > 0) {
			$single = false;
			foreach ($this->withTokens as $pi => $p) {
				$vis++;
				if (!array_key_exists($pi, $this->withTokens)) continue;
				$doStep = array_intersect_key($p->postset, $enabled);
				if (count($doStep) === 1) {
					$vis += 3;
					$t = array_shift($doStep);
					//echo $this->id . ': Execute ' . $t->id . PHP_EOL;
					//unset($this->withTokens[$pi]);
					$checkOR = count($t->postset) >= 2 && $t->simulatesOR;
					$hasTokens = array_intersect_key($this->withTokens, $t->preset);
					$this->withTokens = array_diff_key($this->withTokens, $t->preset);
					$this->executed = array_merge($this->executed, array_values($hasTokens));
					if (!$checkOR) {
						$this->executed[] = $t;
						$this->withTokens += $t->postset;
						$single = true;
					} else {
						return $this->generateORInstances($this->net, $this->withTokens + [], array_merge($this->executed, []), $t);
					}
				}
			}
			if ($single) {
				$this->visitedNodes += $vis;
				return $this->step();
			} else {
				// We have to perform a decision, e.g., derive new instances.
				$instances = [];
				foreach ($this->withTokens as $pi => $p) {
					$vis++;
					$doStep = array_intersect_key($p->postset, $enabled);
					if (count($doStep) >= 1) {
						foreach ($doStep as $ti => $t) {
							$vis += 5;
							$withTokens = $this->withTokens + [];
							unset($withTokens[$pi]);
							$executed = $this->executed + [];
							$executed[] = $p;
							$checkOR = count($t->postset) >= 2 && $t->simulatesOR;
							if (!$checkOR) {
								$executed[] = $t;
								$withTokens += $t->postset;
								$instance = new RunNet($this->net, $withTokens, $executed);
								$instances[$instance->id] = $instance;
							} else {
								$instances += $this->generateORInstances($this->net, $withTokens, $executed, $t);
							}
						}
					}
				}
				$this->visitedNodes += $vis;
				return $instances;
			}
		} else {
			$this->visitedNodes += $vis;
			$this->executed = array_merge($this->executed, array_values($this->withTokens));
			return [];
		}
	}
	
	private function generateORInstances(Net $net, array $withTokens, array $executed, Transition $t) : array {
		$vis = 0;
		$executed[] = $t;
		$instances = [];
		$combis = $this->combinations($t->postset);
		foreach ($combis as $combi) {
			$vis += 3;
			$executedCopy = array_merge($executed, []);
			$instance = new RunNet($this->net, $withTokens + $combi, $executedCopy);
			$instances[$instance->id] = $instance;
		}
		$this->visitedNodes += $vis;
		/*echo "Generated " . count($instances) . " for " . $t->id . " with " . count($t->postset) . " postset size" . PHP_EOL;
		foreach ($instances as $instance) echo "\t" . $instance->out() . PHP_EOL;*/
		
		return $instances;		
	}
	
	private function combinations(array $items) : array {
		$combis = [[]];
		$vis = 0;

		foreach ($items as $el) {
			$vis++;
			foreach ($combis as $combination) {
				$vis++;
				array_push($combis, [ $el->id => $el ] + $combination);
			}
		}
		array_shift($combis);
		$this->visitedNodes += $vis;

		return $combis;
	}
	
	private ?array $contains = null;
	public function getContains() : array {
		if ($this->contains) return $this->contains;
		$this->visitedNodes += count($this->executed);
		$this->contains = array_reduce($this->executed, function (array $con, Node $n) {
			$con[$n->id] = $n;
			return $con;
		}, []);
		return $this->contains;
	}
	
	public function out() : string {
		return 'Instance ' . $this->id . ': ' . json_encode(array_map(function(Node $n) { return $n->id; }, $this->executed)) . " With tokens: " . json_encode(array_keys($this->withTokens));
	}

}
?>