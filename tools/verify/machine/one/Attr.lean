import Lean

/-- The lemmas that say which instruction of `merge` is at which address. -/
register_simp_attr merge_at

/-- The lemmas that say which instruction of the two kernels is at which address. -/
register_simp_attr kcode_at
