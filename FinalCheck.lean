import FRD

example : FRD := frd
example : FRDStrong := frdStrong

/-- info: 'frd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frd

/-- info: 'frdStrong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frdStrong
