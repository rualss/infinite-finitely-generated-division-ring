import FRD.Core.Main
import FRD.FRD1

theorem frdStrong : FRDStrong := FRD.frdStrong_of_frd1 FRD.frd1

theorem frd : FRD := by
  obtain ⟨D, i1, i2, a, b, Y, t, s, h1, h2, h3, _⟩ := frdStrong
  exact ⟨D, i1, i2, a, b, Y, t, s, h1, h2, h3⟩
