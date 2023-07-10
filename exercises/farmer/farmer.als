module farmer

/*
 * The classic river crossing puzzle. A farmer is carrying a fox, a
 * chicken, and a sack of grain. The farmer must cross a river using a boat
 * that can only hold the farmer and at most one other thing. If the
 * farmer leaves the fox alone with the chicken, the fox will eat the
 * chicken; and if the chicken is left alone with the grain, it
 * will eat the grain. How can the farmer bring everything
 * to the far side of the river intact?
 *
 */

open util/ordering[State] as ord

/**
 * The farmer and all his possessions will be represented as Objects.
 * Some objects eat other objects when the Farmer's not around.
 */
abstract sig Object { 
	eats: set Object 
}
one sig Farmer, Fox, Chicken, Grain extends Object {}

/**
 * Define what eats what when the Farmer' not around.
 * Fox eats the chicken and the chicken eats the grain.
 */
fact eating { 
	eats = Fox -> Chicken + Chicken -> Grain
}


/**
 * The near and far relations contain the objects held on each
 * side of the river in a given state, respectively.
 */
sig State {
   near: set Object,
   far: set Object
}

/**
 * In the initial state, all objects are on the near side.
 */
fact initialState {
   let s_init = ord/first |	// s_init is the initial state
     s_init.near = Object && no s_init.far
}

/**
 * Constrains at most one item to move from 'from' to 'to'.
 * Also constrains which objects get eaten.
 */
pred crossRiver [from0, from1, to0, to1: set Object] {
   // either the Farmer takes no items
   (from1 = from0 - Farmer - from1.eats and
    to1 = to0 + Farmer) or
    // or the Farmer takes item "x"
    (some x : from0 - Farmer | 
       from1 = from0 - Farmer - x - from1.eats and
       to1 = to0 + Farmer)
}

/**
 * crossRiver transitions between states
 */
fact stateTransition {
  // s' is the next state of s
  all s0: State, s1: ord/next[s0] {
    Farmer in s0.near implies crossRiver[s0.near, s1.near, s0.far, s1.far]
    Farmer in s0.far implies crossRiver[s0.far, s1.far, s0.near, s1.near]
  }
}

/**
 * In the last state,
 * the farmer has moved everything to the far side of the river.
 */
pred solvePuzzle {
  let lastState = ord/last |
     lastState.far = Fox + Chicken + Grain
}

run solvePuzzle for 6 State
