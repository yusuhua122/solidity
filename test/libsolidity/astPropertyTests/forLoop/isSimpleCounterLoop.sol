contract C {
  function f() public pure {
     /// PositiveCase1: isSimpleCounterLoop
     for(uint i = 0; i < 42; ++i) {
     }
     /// PositiveCase2: isSimpleCounterLoop
     for(int i = 0; i < 42; i++) {
     }
     /// NegativeCase1: isSimpleCounterLoop
     for(uint i = 0; i < 42; i = i + 1) {
     }
     /// NegativeCase2: isSimpleCounterLoop
     for(uint i = 42; i > 0; --i) {
     }
     /// NegativeCase3: isSimpleCounterLoop
     for(uint i = 42; i > 0; i--) {
     }
     /// NegativeCase4: isSimpleCounterLoop
     for(uint i = 1; i < 42; i = i * 2) {
     }
  }
}
// ----
// PositiveCase1: true
// PositiveCase2: true
// NegativeCase1: false
// NegativeCase2: false
// NegativeCase3: false
// NegativeCase4: false
