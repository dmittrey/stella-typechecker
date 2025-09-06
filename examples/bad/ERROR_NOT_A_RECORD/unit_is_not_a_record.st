language core;
extend with #records, #unit-type;

fn main(u : Unit) -> Nat {
  return u.field
}
