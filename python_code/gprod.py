from group_ops import add, multiply, Z1
from secrets import randbelow

from fiat_shamir import hash_integers
from utils import compute_multiexp, compute_innerprod, inverse, curve_order, int_to_binaryintarray


def gprod_prove_outer(current_hash, crs, vec_a, len_gprod, gprod, n, logn):

    [crs_g, u, crs_se1, crs_se2] = crs[:]

    vec_b = [0] * n
    vec_b[0] = 1
    for i in range(1,len_gprod):
        vec_b[i] = vec_a[i] * vec_b[i-1] % curve_order

    for i in range(len_gprod,n):
        vec_b[i] = randbelow(curve_order)

    B = compute_multiexp(crs_g[:], vec_b[:])
    blinder = compute_innerprod(vec_a[len_gprod:],vec_b[len_gprod:])

    current_hash = hash_integers([current_hash, gprod, blinder, int(B[0]), int(B[1]), int(B[2])])
    x = current_hash % curve_order; inv_x =inverse(x);

    vec_c = [0] * n;
    pow_x = x;
    pow_x2 = 1
    for i in range(len_gprod-1):
        vec_c[i] = ( vec_a[i+1] * pow_x  - pow_x2) % curve_order
        pow_x = pow_x * x % curve_order
        pow_x2 = pow_x2 * x % curve_order

    vec_c[len_gprod-1] = (vec_a[0] * pow_x - pow_x2) % curve_order

    pow_x = pow_x * x % curve_order
    for i in range(len_gprod, n):
        vec_c[i] = (vec_a[i] * pow_x) % curve_order

    crs_h = [0]*n; pow_inv_x = inv_x
    for i in range(len_gprod - 1):
        crs_h[i] = multiply(crs_g[i+1], pow_inv_x)
        pow_inv_x = pow_inv_x * inv_x % curve_order
    crs_h[len_gprod-1] = multiply(crs_g[0], pow_inv_x)

    pow_inv_x = pow_inv_x * inv_x % curve_order
    for i in range(len_gprod, n):
        crs_h[i] = multiply(crs_g[i], pow_inv_x)

    inner_prod = (blinder * (x ** (len_gprod+1)) + gprod * (x ** len_gprod) - 1) % curve_order

    crs = [crs_g[:],crs_h[:],u]

#    [current_hash, inner_proof] = gprod_prove_inner(current_hash, crs[:], vec_b[:], vec_c[:], inner_prod, n, logn)

    inner_prod_info = [crs_h[:], vec_b[:], vec_c[:], inner_prod]

    return [current_hash, [B, blinder], inner_prod_info[:]]

def gprod_prove_inner(current_hash, crs, vec_b, vec_c,inner_prod, n, logn):
    [crs_g, crs_h, u] = crs[:]
    proof = []

    ### Adding in zero knowledge
    vec_r = [0]*n;
    for i in range(n):
        vec_r[i] = randbelow(curve_order)

    R = compute_multiexp(crs_h[:], vec_r[:])
    blinder_2 = compute_innerprod(vec_b[:], vec_r[:])

    current_hash = hash_integers([current_hash,int(R[0]),int(R[1]), int(R[2]), blinder_2])
    x = current_hash % curve_order

    inner_prod = (inner_prod + blinder_2 * x ) % curve_order
    for i in range(n):
        vec_c[i] = (vec_c[i] + vec_r[i] * x) % curve_order


    ### Inserting inner_prod into exponent.
    current_hash = hash_integers([current_hash,inner_prod])
    x = current_hash % curve_order;
    u = multiply(u, x)

    for j in range(logn):
        n = n // 2

        zL = compute_innerprod(vec_b[n:], vec_c[:n])
        zR = compute_innerprod(vec_b[:n], vec_c[n:])

        CL = add(compute_multiexp(crs_g[:n], vec_b[n:]), compute_multiexp(crs_h[n:],vec_c[:n]))
        CL = add(CL, multiply(u, zL))
        CR = add(compute_multiexp(crs_g[n:], vec_b[:n]), compute_multiexp(crs_h[:n],vec_c[n:]))
        CR = add(CR, multiply(u, zR))

        proof.append([CL, CR])

        current_hash = hash_integers([current_hash,int(CL[0]),int(CL[1]), int(CL[2]),
        int(CR[0]), int(CR[1]), int(CR[2])])

        x = current_hash % curve_order; inv_x =inverse(x);

        for i in range(n):
            crs_g[i] = add(multiply(crs_g[n + i],inv_x), crs_g[i] )
            crs_h[i] = add(multiply(crs_h[n + i],x), crs_h[i] )
            vec_b[i] =  (vec_b[i] + x * vec_b[n + i] ) % curve_order
            vec_c[i] =  (vec_c[i] + inv_x * vec_c[n + i] ) % curve_order

        crs_g = crs_g[:n]; crs_h = crs_h[:n]
        vec_b = vec_b[:n]; vec_c = vec_c[:n]

    return [current_hash, [R, blinder_2, proof[:], vec_b[0], vec_c[0]]]

def gprod_verify_outer(current_hash, crs, A, len_gprod, gprod, gprod_proof, n, logn):

    [crs_g, u, crs_se1, crs_se2] = crs[:]
    [B, blinder] = gprod_proof[:]

    current_hash = hash_integers([current_hash, gprod, blinder, int(B[0]), int(B[1]), int(B[2])])
    x = current_hash % curve_order; inv_x =inverse(x);

    C = crs_g[0]
    for i in range(1,len_gprod):
        C = add( C, crs_g[i])

    C = multiply(C, curve_order - inv_x)
    C = add(C, A)

    vec_crs_h_exp = [1]*n; pow_inv_x = inv_x
    for i in range(1,len_gprod):
        vec_crs_h_exp[i] = pow_inv_x
        pow_inv_x = pow_inv_x * inv_x % curve_order

    vec_crs_h_exp[0] = pow_inv_x

    pow_inv_x = pow_inv_x * inv_x % curve_order
    for i in range(len_gprod, n):
        vec_crs_h_exp[i] = pow_inv_x

    inner_prod = (blinder * (x ** (len_gprod+1)) + gprod * (x ** len_gprod) - 1) % curve_order

#    [current_hash, b] = gprod_verify_inner(current_hash, crs[:], vec_crs_h_exp[:], C, inner_prod, inner_proof[:],
#    len_gprod, n, logn)

    inner_prod_info = [vec_crs_h_exp[:], B, C, inner_prod, len_gprod]

    return [current_hash, inner_prod_info[:]]

def gprod_verify_inner(current_hash, crs, vec_crs_h_exp, C, inner_prod, inner_proof, len_gprod, n, logn):
    [crs_g, crs_h, u] = crs[:]

    ### Adding in zero knowledge
    [R, blinder_2,proof, last_b, last_c] = inner_proof[:]


    current_hash = hash_integers([current_hash,int(R[0]),int(R[1]), int(R[2]), blinder_2])
    x = current_hash % curve_order

    inner_prod = (inner_prod + blinder_2 * x ) % curve_order
    C = add(C, multiply(R,x))

    ### Putting inner_prod into exponent.
    current_hash = hash_integers([current_hash,inner_prod])
    x = current_hash % curve_order;

    u = multiply(u, x)
    C = add(C, multiply(u,inner_prod))

    vec_crs_g_exp = [1] * n;
    vec_crs_h_shifted = [1] * n;

    n_var = n
    for j in range(logn):
        n_var = n_var // 2
        [CL, CR] = proof[j]

        current_hash = hash_integers([current_hash,int(CL[0]),int(CL[1]), int(CL[2]),
                int(CR[0]), int(CR[1]), int(CR[2])])

        x = current_hash % curve_order; inv_x =inverse(x)

        for i in range(n):
            bin_i = int_to_binaryintarray(i,logn)
            if bin_i[logn - j - 1] == 1:
                vec_crs_g_exp[i] = (vec_crs_g_exp[i] * inv_x) % curve_order
                vec_crs_h_shifted[i] = (vec_crs_h_shifted[i] * x) % curve_order

        C = add(add(multiply(CR, inv_x), C), multiply(CL, x))

    vec_crs_h_exp[0] = (vec_crs_h_exp[0] * vec_crs_h_shifted[len_gprod - 1]) % curve_order
    for i in range(1,len_gprod):
        vec_crs_h_exp[i] = (vec_crs_h_exp[i] * vec_crs_h_shifted[i-1]) % curve_order
    for i in range(len_gprod,n):
        vec_crs_h_exp[i] = (vec_crs_h_exp[i] * vec_crs_h_shifted[i]) % curve_order

    inner_prod = last_b * last_c % curve_order
    final_g = compute_multiexp(crs_g[:], vec_crs_g_exp[:])
    final_h = compute_multiexp(crs_h[:], vec_crs_h_exp[:])

    expected_outcome = multiply(final_g, curve_order - last_b)
    expected_outcome = add(expected_outcome, multiply(final_h, curve_order - last_c))
    expected_outcome = add(expected_outcome, multiply(u, curve_order - inner_prod))

    if add( expected_outcome, C) != (1,1,0):
        print("ERROR: final exponent is incorrect")
        return [current_hash, 0]

    return [current_hash, 1]
