language core;

extend with  #letrec-bindings;

fn foo(n : Nat) -> Nat {
	return n
}

fn main(n : Nat) -> Nat {
    return letrec x = 0 in x
}

//ERROR_AMBIGUOUS_PATTERN_TYPE
