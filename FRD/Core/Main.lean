import FRD.Core.Tower
import FRD.Core.Final

namespace FRD

theorem frdStrong_of_frd1 (h : FRD1) : FRDStrong := by
  obtain ⟨L, _, _, a, b, y, hy⟩ := Core.exists_solution h
  exact Core.frdStrong_of_solution a b y hy

end FRD
