import data.cpi.semantics.with_normalise data.cpi.semantics.ode

def ℍ : Type := fin_poly raw_string ℚ
instance : half_ring ℍ := fin_poly.half_ring string ℚ
instance : has_repr ℍ := fin_poly.has_repr string ℚ

def ℂ : Type := ℍ
instance : half_ring ℂ := fin_poly.half_ring _ _
instance : has_repr ℂ := fin_poly.has_repr _ _

def conc : ℍ ↪ ℂ := function.embedding.refl _
