from group_ops import add, multiply, Z1
from secrets import randbelow

from fiat_shamir import hash_integers
from utils import compute_multiexp, compute_innerprod, inverse, curve_order, int_to_binaryintarray

def prove_multiexp_and_gprod_inner(current_hash, crs, vec_b, vec_c,inner_prod,
ciphertexts_1, ciphertexts_2, vec_exp, n, logn):
    [crs_g, crs_h, crs_h_scaled, u] = crs[:]

    proof = []

    ### Adding in zero knowledge
    vec_rgp = [0]*n; vec_rme = [0]*n;
    for i in range(n):
        vec_rgp[i] = randbelow(curve_order)
        vec_rme[i] = randbelow(curve_order)

    Rgp = compute_multiexp(crs_h_scaled[:], vec_rgp[:])
    blgp = compute_innerprod(vec_b[:], vec_rgp[:])

    Rme = compute_multiexp(crs_h[:], vec_rme[:])
    Bl1me = compute_multiexp(ciphertexts_1[:], vec_rme[:])
    Bl2me = compute_multiexp(ciphertexts_2[:], vec_rme[:])

    zkinfo = [Rgp, Rme, blgp, Bl1me, Bl2me]

    current_hash = hash_integers([current_hash,int(Rgp[0]),int(Rgp[1]), int(Rgp[2]), blgp,
    int(Rme[0]),int(Rme[1]), int(Rme[2]),
    int(Bl1me[0]),int(Bl1me[1]), int(Bl1me[2]),int(Bl2me[0]),int(Bl2me[1]), int(Bl2me[2])])
    x = current_hash % curve_order

    inner_prod = (inner_prod + blgp * x ) % curve_order
    for i in range(n):
        vec_c[i] = (vec_c[i] + vec_rgp[i] * x) % curve_order
        vec_exp[i] = (vec_exp[i] + vec_rme[i] * x) % curve_order


    ### Inserting inner_prod into exponent.
    current_hash = hash_integers([current_hash,inner_prod])
    x = current_hash % curve_order;
    u = multiply(u, x)

    for j in range(logn):
        n = n // 2

        zLgp = compute_innerprod(vec_b[n:], vec_c[:n])
        zRgp = compute_innerprod(vec_b[:n], vec_c[n:])
        zLme = [compute_multiexp(ciphertexts_1[n:], vec_exp[:n]), compute_multiexp(ciphertexts_2[n:], vec_exp[:n])]
        zRme = [compute_multiexp(ciphertexts_1[:n], vec_exp[n:]), compute_multiexp(ciphertexts_2[:n], vec_exp[n:])]

        CLgp = add(compute_multiexp(crs_g[:n], vec_b[n:]), compute_multiexp(crs_h_scaled[n:],vec_c[:n]))
        CLgp = add(CLgp, multiply(u, zLgp))
        CRgp = add(compute_multiexp(crs_g[n:], vec_b[:n]), compute_multiexp(crs_h_scaled[:n],vec_c[n:]))
        CRgp = add(CRgp, multiply(u, zRgp))
        CLme = compute_multiexp(crs_h[n:], vec_exp[:n])
        CRme = compute_multiexp(crs_h[:n], vec_exp[n:])

        proof.append([CLgp, CRgp, zLme, zRme, CLme, CRme])

        current_hash = hash_integers([current_hash,int(CLgp[0]),int(CLgp[1]), int(CLgp[2]),
        int(CRgp[0]), int(CRgp[1]), int(CRgp[2]), int(zLme[0][0]), int(zLme[0][1]), int(zLme[0][2]),
        int(zRme[0][0]), int(zRme[0][1]), int(zRme[0][2]), int(CLme[0]),int(CLme[1]), int(CLme[2]),
        int(CRme[0]), int(CRme[1]), int(CRme[2])])

        x = current_hash % curve_order; inv_x =inverse(x);

        for i in range(n):
            crs_g[i] = add(multiply(crs_g[n + i],inv_x), crs_g[i] )
            crs_h_scaled[i] = add(multiply(crs_h_scaled[n + i],x), crs_h_scaled[i] )
            vec_b[i] =  (vec_b[i] + x * vec_b[n + i] ) % curve_order
            vec_c[i] =  (vec_c[i] + inv_x * vec_c[n + i] ) % curve_order

            crs_h[i] = add(multiply(crs_h[n + i],x), crs_h[i] )
            ciphertexts_1[i] = add(multiply(ciphertexts_1[n + i], x), ciphertexts_1[i])
            ciphertexts_2[i] = add(multiply(ciphertexts_2[n + i], x), ciphertexts_2[i])

            vec_exp[i] = (vec_exp[n + i] * inv_x + vec_exp[i]) % curve_order

        crs_g = crs_g[:n]; crs_h_scaled = crs_h_scaled[:n]
        vec_b = vec_b[:n]; vec_c = vec_c[:n]

        crs_h = crs_h[:n]
        ciphertexts_1 = ciphertexts_1[:n]
        ciphertexts_2 = ciphertexts_2[:n]

        vec_exp = vec_exp[:n]

    final_values = [vec_b[0], vec_c[0], vec_exp[0]]
    current_hash = hash_integers([current_hash, vec_b[0], vec_c[0], vec_exp[0]])

    return [current_hash, [zkinfo[:], proof[:], final_values[:]]]

def verify_multiexp_and_gprod_inner(current_hash, crs, vec_crs_h_exp, len_gprod, C, inner_prod,
  ciphertexts_1, ciphertexts_2, commit_exps, multiexp_1, multiexp_2, inner_proof,n, logn):
    [crs_g, crs_h, u] = crs[:]

    ### Adding in zero knowledge
    [zkinfo, proof, final_values] = inner_proof[:]
    [Rgp, Rme, blgp, Bl1me, Bl2me] = zkinfo[:]

    current_hash = hash_integers([current_hash,int(Rgp[0]),int(Rgp[1]), int(Rgp[2]), blgp,
    int(Rme[0]),int(Rme[1]), int(Rme[2]),
    int(Bl1me[0]),int(Bl1me[1]), int(Bl1me[2]),int(Bl2me[0]),int(Bl2me[1]), int(Bl2me[2])])
    x = current_hash % curve_order

    inner_prod = (inner_prod + blgp * x ) % curve_order
    C = add(C, multiply(Rgp,x))
    commit_exps = add(commit_exps, multiply(Rme, x))
    multiexp_1 = add(multiexp_1, multiply(Bl1me, x))
    multiexp_2 = add(multiexp_2, multiply(Bl2me, x))

    ### Putting inner_prod into exponent.
    current_hash = hash_integers([current_hash,inner_prod])
    x = current_hash % curve_order;

    u = multiply(u, x)
    C = add(C, multiply(u,inner_prod))

    [final_b, final_c, final_exp] = final_values[:]
    vec_crs_g_exp = [final_b] * n;
    vec_crs_h_shifted = [1] * n;

    n_var = n
    for j in range(logn):
        n_var = n_var // 2

        [CLgp, CRgp, zLme, zRme, CLme, CRme] = proof[j]

        current_hash = hash_integers([current_hash,int(CLgp[0]),int(CLgp[1]), int(CLgp[2]),
        int(CRgp[0]), int(CRgp[1]), int(CRgp[2]), int(zLme[0][0]), int(zLme[0][1]), int(zLme[0][2]),
        int(zRme[0][0]), int(zRme[0][1]), int(zRme[0][2]), int(CLme[0]),int(CLme[1]), int(CLme[2]),
        int(CRme[0]), int(CRme[1]), int(CRme[2])])

        x = current_hash % curve_order; inv_x =inverse(x)

        for i in range(n):
            bin_i = int_to_binaryintarray(i,logn)
            if bin_i[logn - j - 1] == 1:
                vec_crs_g_exp[i] = (vec_crs_g_exp[i] * inv_x) % curve_order
                vec_crs_h_shifted[i] = (vec_crs_h_shifted[i] * x) % curve_order

        C = add(add(multiply(CRgp, inv_x), C), multiply(CLgp, x))
        multiexp_1 = add(add( multiply(zLme[0],x), multiexp_1 ), multiply(zRme[0], inv_x) )
        multiexp_2 = add(add( multiply(zLme[1],x), multiexp_2 ), multiply(zRme[1], inv_x) )

        commit_exps = add(add(multiply(CRme, inv_x), commit_exps), multiply(CLme, x))

    ciphertexts_1_final = compute_multiexp(ciphertexts_1[:], vec_crs_h_shifted[:])
    ciphertexts_2_final = compute_multiexp(ciphertexts_2[:], vec_crs_h_shifted[:])

    if add( multiply(ciphertexts_1_final, curve_order - final_exp), multiexp_1) != (1,1,0):
        print("ERROR: final ciphertext 1 is incorrect")
        return [current_hash, 0]

    if add( multiply(ciphertexts_2_final, curve_order - final_exp), multiexp_2) != (1,1,0):
        print("ERROR: final ciphertext 2 is incorrect")
        return [current_hash, 0]

    current_hash = hash_integers([current_hash, final_b, final_c, final_exp])
    x = current_hash % curve_order

    vec_crs_h_exp[0] = ( x * vec_crs_h_shifted[0] * final_exp +
    vec_crs_h_exp[0] * vec_crs_h_shifted[len_gprod - 1] * final_c) % curve_order
    for i in range(1,len_gprod):
        vec_crs_h_exp[i] = (x * vec_crs_h_shifted[i] * final_exp +
        vec_crs_h_exp[i] * vec_crs_h_shifted[i-1] * final_c) % curve_order

    for i in range(len_gprod,n):
        vec_crs_h_exp[i] = (x * vec_crs_h_shifted[i] * final_exp
        + vec_crs_h_exp[i] * vec_crs_h_shifted[i] * final_c) % curve_order

    inner_prod = final_b * final_c % curve_order
#    final_g = compute_multiexp(crs_g[:], vec_crs_g_exp[:])
#    final_h = compute_multiexp(crs_h[:], vec_crs_h_exp[:])

    expected_outcome = compute_multiexp(crs_g[:], vec_crs_g_exp[:])
    expected_outcome = add(expected_outcome, compute_multiexp(crs_h[:], vec_crs_h_exp[:]))
    expected_outcome = add(expected_outcome, multiply(u, inner_prod))

    expected_outcome = add(expected_outcome, multiply(C, curve_order - 1))
    expected_outcome = add(expected_outcome, multiply(commit_exps, curve_order - x))

    if expected_outcome != Z1:
        print("ERROR: final exponent is incorrect")
        return [current_hash, 0]

    return [current_hash, 1]
