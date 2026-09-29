import MinModulus.Main.Certificate
import MinModulus.CheckerSound.Assembly

/-!
# The numeric certificate (formerly the stub of the integration)

STATUS: no `sorry` in this file. Owned by CS-D (checker soundness, assembly) since the checker
landed.

`cert_16000` is now `MinModulus.CheckerSound.D.cert_16000` (`CheckerSound/Assembly.lean`): the
certificate `Cert 16000 (2·10^8) δ₀ c₀ T₀` with
* `δ₀ = CheckerSound.delta0 fullParams` (`deltaN fullParams p / 10^9` for `p ≤ 2·10^8`, `1/2`
  beyond),
* `c₀ p = costOf (run fullParams) fullParams p / 2^62`,
* `T₀ = (run fullParams).T / 2^62`,
from the executable checker `CheckerImpl.check` (`check_eq_true`, by `native_decide`) and the
code-level soundness proof in `MinModulus/CheckerSound/`.

The statement below is exactly what `Main.not_covers_of_cert` consumes (unchanged).
-/

namespace MinModulus.Main.Stub

/-- The numeric certificate for the minimum modulus `m = 16000` with tail threshold
`X = 2·10^8` (`CheckerImpl` + `CheckerSound`). -/
theorem cert_16000 : ∃ (δ c : ℕ → ℝ) (T : ℝ), Cert 16000 (2 * 10 ^ 8) δ c T :=
  MinModulus.CheckerSound.D.cert_16000

end MinModulus.Main.Stub
