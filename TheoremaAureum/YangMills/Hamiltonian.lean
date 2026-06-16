-- TheoremaAureum.YangMills.Hamiltonian
-- Abstract Wilson transfer-matrix Hamiltonian schema.

namespace TheoremaAureum.YangMills

noncomputable def wilsonHamiltonian (β : ℝ) : ℝ := β

theorem wilsonHamiltonian_nonneg (β : ℝ) (h : β ≥ 0) :
    wilsonHamiltonian β ≥ 0 := h

end TheoremaAureum.YangMills
