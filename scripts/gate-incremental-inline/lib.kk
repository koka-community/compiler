module lib

extern import
  c file "lib-inline.c"

pub extern k(): int
  c "kk_gate_k"
