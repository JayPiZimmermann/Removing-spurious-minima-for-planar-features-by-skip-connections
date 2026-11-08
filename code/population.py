"""Float64 closed forms for the fixed Gaussian population experiments."""
import numpy as np

PI = np.pi
UNIT_TOL = 64.0 * np.finfo(np.float64).eps
GRAM_TOL = 128.0 * np.finfo(np.float64).eps
ZERO_TOL = 1e-10
_PSI_ANTIPODAL_CUTOFF = -0.9


def _as_correlations(rho, name="rho"):
    """Return finite correlations in [-1, 1]."""
    rho = np.asarray(rho, dtype=np.float64)
    if not np.all(np.isfinite(rho)):
        raise ValueError(f"{name}: correlations must all be finite")
    bad = np.abs(rho) > 1.0
    if np.any(bad):
        flat_index = int(np.flatnonzero(bad)[0])
        first = tuple(int(i) for i in np.unravel_index(flat_index, rho.shape))
        value = float(rho[first]) if first else float(rho)
        raise ValueError(
            f"{name}: correlation outside [-1, 1] at index {first}: {value}"
        )
    return rho


def Phi(rho):
    """Centered kernel: rho*arcsin(rho) + sqrt(1-rho**2)."""
    rho = _as_correlations(rho)
    val = rho * np.arcsin(rho) + np.sqrt(np.maximum(0.0, 1.0 - rho * rho))
    return np.where(np.abs(rho) == 1.0, PI / 2.0, val)


def Psi(rho):
    """Plain-ReLU kernel, with a stable series near rho=-1."""
    rho = _as_correlations(rho)
    direct = Phi(rho) + (PI / 2.0) * rho
    delta = 2.0 * np.arcsin(np.sqrt(0.5 * (1.0 + rho)))
    z = delta * delta
    series_factor = (
        1.0 / 3.0
        + z * (
            -1.0 / 30.0
            + z * (
                1.0 / 840.0
                + z * (
                    -1.0 / 45360.0
                    + z * (
                        1.0 / 3991680.0
                        + z * (
                            -1.0 / 518918400.0
                            + z * (1.0 / 93405312000.0 - z / 22230464256000.0)
                        )
                    )
                )
            )
        )
    )
    stable = delta * z * series_factor
    return np.where(rho <= _PSI_ANTIPODAL_CUTOFF, stable, direct)


def Phi_d(rho):
    """Derivative of Phi with respect to its correlation argument."""
    rho = _as_correlations(rho)
    return np.arcsin(rho)


def Psi_d(rho):
    """Derivative of Psi with an antipodal half-angle evaluation."""
    rho = _as_correlations(rho)
    direct = Phi_d(rho) + PI / 2.0
    stable = 2.0 * np.arcsin(np.sqrt(0.5 * (1.0 + rho)))
    return np.where(rho <= _PSI_ANTIPODAL_CUTOFF, stable, direct)


def validate_directions(W, name="directions"):
    """Validate near-unit direction rows and normalize roundoff-sized errors."""
    W = np.asarray(W, dtype=np.float64)
    if W.ndim != 2:
        raise ValueError(f"{name}: expected a 2D (k, d) array, got shape {W.shape}")
    if not np.all(np.isfinite(W)):
        raise ValueError(f"{name}: all direction entries must be finite")
    norms = np.linalg.norm(W, axis=1)
    zero_rows = np.nonzero(norms <= ZERO_TOL)[0]
    if zero_rows.size:
        raise ValueError(
            f"{name}: zero (or near-zero, norm<={ZERO_TOL}) row(s) at indices "
            f"{zero_rows.tolist()} -- direction undefined, refusing to silently "
            f"normalize or clip"
        )
    bad_rows = np.nonzero(np.abs(norms - 1.0) > UNIT_TOL)[0]
    if bad_rows.size:
        raise ValueError(
            f"{name}: row(s) at indices {bad_rows.tolist()} are not unit-norm "
            f"within tol={UNIT_TOL} (norms={norms[bad_rows].tolist()})"
        )
    return W / norms[:, None]


def _as_masses(x, name="masses", expected=None):
    x = np.asarray(x, dtype=np.float64)
    if x.ndim != 1:
        raise ValueError(f"{name}: expected a 1D vector, got shape {x.shape}")
    if expected is not None and x.shape != (expected,):
        raise ValueError(f"{name}: expected shape ({expected},), got shape {x.shape}")
    if not np.all(np.isfinite(x)):
        raise ValueError(f"{name}: all entries must be finite")
    return x


def _validated_gram(A, B, name, *, self_gram=False):
    """Compute a Gram block, accepting only roundoff-sized domain violations."""
    G = A @ B.T
    if not np.all(np.isfinite(G)):
        raise ValueError(f"{name}: Gram correlations must all be finite")
    bad = np.argwhere(np.abs(G) > 1.0 + GRAM_TOL)
    if bad.size:
        first = tuple(int(i) for i in bad[0])
        raise ValueError(
            f"{name}: correlation outside [-1, 1] beyond GRAM_TOL at "
            f"index {first}: {float(G[first])}"
        )
    if self_gram:
        diagonal = np.diag(G)
        if not np.all(np.abs(diagonal - 1.0) <= GRAM_TOL):
            raise ValueError(f"{name}: Gram diagonal is not unit within GRAM_TOL")
    return np.clip(G, -1.0, 1.0)


def _population_inputs(c, W, s, V):
    W = validate_directions(W, name="W")
    V = validate_directions(V, name="V")
    if W.shape[1] != V.shape[1]:
        raise ValueError(
            f"W and V must share an ambient dimension, got {W.shape[1]} and {V.shape[1]}"
        )
    c = _as_masses(c, name="c", expected=W.shape[0])
    s = _as_masses(s, name="s", expected=V.shape[0])
    return c, W, s, V


def _pop_loss(c, W, s, V, kf):
    c, W, s, V = _population_inputs(c, W, s, V)
    Gss = _validated_gram(W, W, "W-W", self_gram=True)
    Gst = _validated_gram(W, V, "W-V")
    Gtt = _validated_gram(V, V, "V-V", self_gram=True)
    total = (
        0.5 * np.einsum("i,j,ij->", c, c, kf(Gss))
        - np.einsum("i,k,ik->", c, s, kf(Gst))
        + 0.5 * np.einsum("k,l,kl->", s, s, kf(Gtt))
    )
    return total / (2.0 * PI)


def L_C(c, W, s, V):
    """Centered Gaussian population half-squared loss."""
    return _pop_loss(c, W, s, V, Phi)


def L_R(c, W, s, V):
    """Plain-ReLU Gaussian population half-squared loss."""
    return _pop_loss(c, W, s, V, Psi)


def skip_delta(c, W, s, V, b_star):
    """Linear mismatch delta = (c@W)/2 - b_star - (s@V)/2."""
    c, W, s, V = _population_inputs(c, W, s, V)
    b_star = _as_masses(b_star, name="b_star", expected=W.shape[1])
    return 0.5 * (c @ W) - b_star - 0.5 * (s @ V)


def L_skip(b, c, W, s, V, b_star):
    """Joint plain-ReLU skip loss, using the centered-loss decomposition."""
    W_checked = validate_directions(W, name="W")
    b = _as_masses(b, name="b", expected=W_checked.shape[1])
    b_star = _as_masses(b_star, name="b_star", expected=W_checked.shape[1])
    mism = b - b_match(c, W, s, V, b_star)
    return L_C(c, W, s, V) + 0.5 * float(np.sum(mism ** 2))


def b_match(c, W, s, V, b_star):
    """Matching skip vector for the joint plain-ReLU objective."""
    return -skip_delta(c, W, s, V, b_star)


def _direction_gradient_views(formal_lift, W_unit):
    """Return formal and sphere-tangent direction gradients."""
    formal_lift = np.asarray(formal_lift, dtype=np.float64)
    radial = np.einsum("id,id->i", W_unit, formal_lift)
    tangent = formal_lift - radial[:, None] * W_unit
    return {
        "grad_W_formal_lift": formal_lift,
        "grad_W_tan": tangent,
    }


def _grad_pop(c, W, s, V, kf, kfd):
    """Shared mass and direction gradient calculation for L_C and L_R."""
    c, W, s, V = _population_inputs(c, W, s, V)
    Gss = _validated_gram(W, W, "W-W", self_gram=True)
    Gst = _validated_gram(W, V, "W-V")
    Kss = kf(Gss)
    Kst = kf(Gst)
    dGss = kfd(Gss)
    dGst = kfd(Gst)

    grad_c = (Kss @ c - Kst @ s) / (2.0 * PI)

    term1 = (dGss * c[None, :]) @ W
    term2 = (dGst * s[None, :]) @ V
    grad_W_formal_lift = (c[:, None] * (term1 - term2)) / (2.0 * PI)
    return {"grad_c": grad_c,
            **_direction_gradient_views(grad_W_formal_lift, W)}


def grad_L_C(c, W, s, V):
    """Gradient of the centered population loss."""
    return _grad_pop(c, W, s, V, Phi, Phi_d)


def grad_L_R(c, W, s, V):
    """Gradient of the plain-ReLU population loss."""
    return _grad_pop(c, W, s, V, Psi, Psi_d)


def grad_L_skip(b, c, W, s, V, b_star):
    """Student gradient of L_skip in b, c, and W."""
    c_arr, W_arr, s_arr, V_arr = _population_inputs(c, W, s, V)
    b = _as_masses(b, name="b", expected=W_arr.shape[1])
    b_star_arr = _as_masses(b_star, name="b_star", expected=W_arr.shape[1])
    out = grad_L_C(c_arr, W_arr, s_arr, V_arr)
    u = b + skip_delta(c_arr, W_arr, s_arr, V_arr, b_star_arr)
    out["grad_b"] = u.copy()
    out["grad_c"] = out["grad_c"] + 0.5 * (W_arr @ u)
    grad_W_formal_lift = out["grad_W_formal_lift"] + 0.5 * c_arr[:, None] * u[None, :]
    out.update(_direction_gradient_views(grad_W_formal_lift, W_arr))
    return out
