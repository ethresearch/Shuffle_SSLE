from group_ops import add, multiply, Z1
from secrets import randbelow
from fiat_shamir import hash_integers

from utils import compute_multiexp, curve_order

def multiexp_prove(current_hash, crs, ciphertexts_R, ciphertexts_S, exponents, n,logn):
    proof = []

    ### Adding in zero knowledge
    vec_r = [0]*n;
    for i in range(n):
        vec_r[i] = randbelow(curve_order)

    R = compute_multiexp(crs[:], vec_r[:])
    Rbl = compute_multiexp(ciphertexts_R[:], vec_r[:])
    Sbl = compute_multiexp(ciphertexts_S[:], vec_r[:])

    current_hash = hash_integers([current_hash,int(R[0]),int(R[1]), int(R[2]),
    int(Rbl[0]),int(Rbl[1]), int(Rbl[2]),int(Sbl[0]),int(Sbl[1]), int(Sbl[2])])
    x = current_hash % curve_order

    for i in range(n):
        exponents[i] = (exponents[i] + vec_r[i] * x) % curve_order

    for j in range(logn):
        n = n // 2

        zL = [compute_multiexp(ciphertexts_R[n:], exponents[:n]), compute_multiexp(ciphertexts_S[n:], exponents[:n])]
        zR = [compute_multiexp(ciphertexts_R[:n], exponents[n:]), compute_multiexp(ciphertexts_S[:n], exponents[n:])]
        CL = compute_multiexp(crs[n:], exponents[:n])
        CR = compute_multiexp(crs[:n], exponents[n:])

        proof.append([zL, zR, CL, CR])

        current_hash = hash_integers([current_hash,int(zL[0][0]), int(zL[0][1]),int(zR[0][0]),
        int(zR[0][1]),int(CL[0]),int(CL[1]),int(CR[0]), int(CR[1])])

        x = current_hash % curve_order; inv_x =inverse(x);

        for i in range(n):
            crs[i] = add(multiply(crs[n + i],x), crs[i] )
            ciphertexts_R[i] = add(multiply(ciphertexts_R[n + i], x), ciphertexts_R[i])
            ciphertexts_S[i] = add(multiply(ciphertexts_S[n + i], x), ciphertexts_S[i])

        crs = crs[:n]
        ciphertexts_R = ciphertexts_R[:n]
        ciphertexts_S = ciphertexts_S[:n]

        for i in range(n):
            exponents[i] = (exponents[n + i] * inv_x + exponents[i] ) % curve_order

        exponents = exponents[:n]

    return [current_hash,[R, Rbl, Sbl, proof, exponents[0]]]

def multiexp_verify(current_hash, crs, ciphertexts_R, ciphertexts_S, commit_exps, ip_proof, multiexp_R, multiexp_S, n,logn):
    [R, Rbl, Sbl, proof, last_exp] = ip_proof[:]

    ### Adding zero-knowledge

    current_hash = hash_integers([current_hash,int(R[0]),int(R[1]), int(R[2]),
    int(Rbl[0]),int(Rbl[1]), int(Rbl[2]),int(Sbl[0]),int(Sbl[1]), int(Sbl[2])])
    x = current_hash % curve_order

    commit_exps = add(commit_exps, multiply(R, x))
    multiexp_R = add(multiexp_R, multiply(Rbl, x))
    multiexp_S = add(multiexp_S, multiply(Sbl, x))

    vec_crs_exp = [1] * n
    n_var = n

    for j in range(logn):
        n_var = n_var // 2
        ## print("i = ", i, "commit_exps = ", commit_exps)
        [zL, zR, CL, CR] = proof[j]

        current_hash = hash_integers([current_hash,int(zL[0][0]), int(zL[0][1]),int(zR[0][0]),
        int(zR[0][1]),int(CL[0]),int(CL[1]),int(CR[0]), int(CR[1])])

        x = current_hash; inv_x =inverse(x)

        for i in range(n):
            bin_i = int_to_binaryintarray(i,logn)
            if bin_i[logn - j - 1] == 1:
                vec_crs_exp[i] = (vec_crs_exp[i] * x) % curve_order

        multiexp_R = add(add( multiply(zL[0],x), multiexp_R ), multiply(zR[0], inv_x) )
        multiexp_S = add(add( multiply(zL[1],x), multiexp_S ), multiply(zR[1], inv_x) )

        commit_exps = add(add(multiply(CR, inv_x), commit_exps), multiply(CL, x))


    crs_final = compute_multiexp(crs[:], vec_crs_exp[:])
    R_final = compute_multiexp(ciphertexts_R[:], vec_crs_exp[:])
    S_final = compute_multiexp(ciphertexts_S[:], vec_crs_exp[:])

    if add( multiply(crs_final, curve_order - last_exp), commit_exps) != (1,1,0):
        print("ERROR: final exponent is incorrect")
        return [current_hash, 0]

    if add( multiply(R_final, curve_order - last_exp), multiexp_R) != (1,1,0):
        print("ERROR: final ciphertext R is incorrect")
        return [current_hash, 0]

    if add( multiply(S_final, curve_order - last_exp), multiexp_S) != (1,1,0):
        print("ERROR: final ciphertext S is incorrect")
        return [current_hash, 0]

    return [current_hash, 1]
