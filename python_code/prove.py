from group_ops import add, multiply, Z1
from timeit import default_timer as timer

from random import randint
from secrets import randbelow
import math

from fiat_shamir import hash_integers
from gprod import gprod_prove_outer as gprod_prove, gprod_verify_outer as gprod_verify
from sameexp import sameexp_prove, sameexp_verify
from inner_product import prove_multiexp_and_gprod_inner, verify_multiexp_and_gprod_inner
from utils import compute_multiexp, compute_innerprod, inverse, int_to_binaryintarray, curve_order

def shuffle(ciphertexts_R, ciphertexts_S):
    n = len(ciphertexts_R);
    leftover_values = [0] * n;
    for i in range(n):
        leftover_values[i] = i;

    shuffle = [0] * n
    for i in range(n):
        k = randint(0, n - i - 1 )
        shuffle[i] = leftover_values.pop(k)

    ciphertexts_shuffled_R = [0] * n
    ciphertexts_shuffled_S = [0] * n
    for i in range(n):
        ciphertexts_shuffled_R[i] = ciphertexts_R[shuffle[i]][:]
        ciphertexts_shuffled_S[i] = ciphertexts_S[shuffle[i]][:]

    r = randbelow(curve_order)
    for i in range(n):
        ciphertexts_shuffled_R[i] = multiply(ciphertexts_shuffled_R[i], r)
        ciphertexts_shuffled_S[i] = multiply(ciphertexts_shuffled_S[i], r)


    return (ciphertexts_shuffled_R, ciphertexts_shuffled_S, shuffle, r)


def shuffle_prove(crs, num_blinders, ciphertexts_R, ciphertexts_S, ciphertexts_T, ciphertexts_U, shuffle, r):

    [crs_g, crs_h, u] = crs[:]
    n = len(ciphertexts_R) + num_blinders
    logn = int(math.log(n,2))

    vec_m = [0] * n
    for i in range(len(ciphertexts_R)):
        vec_m[i] = shuffle[i]

    for i in range(len(ciphertexts_R), n):
        vec_m[i] = randbelow(curve_order)

    M = compute_multiexp(crs_h[:], vec_m[:])

    current_hash = hash_integers([int(M[0]), int(M[1]), int(M[2])])
    for i in range(len(ciphertexts_T)):
        current_hash = hash_integers([current_hash, int(ciphertexts_T[i][0]),
        int(ciphertexts_T[i][1]), int(ciphertexts_T[i][2]),
        int(ciphertexts_U[i][0]), int(ciphertexts_U[i][1]),
        int(ciphertexts_U[i][2])])

    print("current_hash = ", current_hash)

    vec_a = [0] * len(ciphertexts_R)
    for i in range(len(ciphertexts_R)):
        vec_a[i] = current_hash % curve_order
        current_hash = hash_integers([current_hash])

    vec_a_shuffled = [0] * n
    for i in range(len(ciphertexts_R)):
        vec_a_shuffled[i] = vec_a[shuffle[i]]

    for i in range(len(ciphertexts_R), n):
        vec_a_shuffled[i] = randbelow(curve_order)

    A = compute_multiexp(crs_h[:], vec_a_shuffled[:])

    current_hash = hash_integers([current_hash, int(M[0]), int(M[1]), int(M[2]),
    int(A[0]), int(A[1]), int(A[2])])
    alpha = current_hash % curve_order

    current_hash = hash_integers([current_hash])
    beta = current_hash % curve_order

    vec_gprod = vec_a_shuffled[:]
    for i in range(n):
        vec_gprod[i] = (vec_gprod[i] + vec_m[i] * alpha + beta ) % curve_order

    gprod = 1
    for i in range(len(ciphertexts_R)):
        gprod = (gprod * vec_gprod[i] ) % curve_order

    A1 = crs_h[0]
    for i in range(1,n):
        A1 = add(A1, crs_h[i])
    A1 = multiply(A1, beta)
    A1 = add(A1, multiply(M, alpha))
    A1 = add(A1, A)

    start = timer()
    [current_hash, gprod_proof, inner_prod_info] = gprod_prove(current_hash, crs[:],
    A1, gprod, vec_gprod[:], len(ciphertexts_R),  n, logn)
    end = timer()
    print("gprod time = ", end - start)

    [crs_h_scaled, vec_b, vec_c, inner_prod] = inner_prod_info[:]

    while len(ciphertexts_T) < n:
        ciphertexts_T.append(Z1)
        ciphertexts_U.append(Z1)

    start = timer()
    R = compute_multiexp(ciphertexts_R[:], vec_a[:])
    S = compute_multiexp(ciphertexts_S[:], vec_a[:])
    end = timer()
    print("R, S time = ", end - start, len(vec_a[:len(ciphertexts_R)]))

    T = multiply(R, r); U = multiply(S, r)

    (current_hash, sameexp_proof) = sameexp_prove(current_hash, R, S, T, U, r)


    start = timer()
    crs = [crs_g[:], crs_h[:], crs_h_scaled[:], u]
    [current_hash, gprod_and_multiexp_proof] = prove_multiexp_and_gprod_inner(current_hash,
    crs[:], vec_b[:], vec_c[:],inner_prod,
    ciphertexts_T[:], ciphertexts_U[:], vec_a_shuffled[:], n, logn)
    end = timer()
    print("inner product time = ", end - start)

    return [M, A, gprod_proof[:], T, U, sameexp_proof, gprod_and_multiexp_proof]

def shuffle_verify(crs, num_blinders, ciphertexts_R, ciphertexts_S, ciphertexts_T, ciphertexts_U, shuffle_proof):

    [crs_g, crs_h, u] = crs[:]
    n = len(ciphertexts_R) + num_blinders
    logn = int(math.log(n,2))

    [M, A, gprod_proof, T, U, sameexp_proof, inner_proof] = shuffle_proof[:]

    start = timer()
    current_hash = hash_integers([int(M[0]), int(M[1]), int(M[2])])
    for i in range(len(ciphertexts_T)):
        current_hash = hash_integers([current_hash, int(ciphertexts_T[i][0]),
        int(ciphertexts_T[i][1]), int(ciphertexts_T[i][2]),
        int(ciphertexts_U[i][0]), int(ciphertexts_U[i][1]),
        int(ciphertexts_U[i][2])])
    end = timer()
    hash_time =  end - start

    vec_a = [0] * len(ciphertexts_R)
    for i in range(len(ciphertexts_R)):
        vec_a[i] = current_hash % curve_order
        current_hash = hash_integers([current_hash])

    current_hash = hash_integers([current_hash, int(M[0]), int(M[1]), int(M[2]),
    int(A[0]), int(A[1]), int(A[2])])
    alpha = current_hash % curve_order

    current_hash = hash_integers([current_hash])
    beta = current_hash % curve_order

    gprod = 1
    for i in range(len(ciphertexts_R)):
        gprod = (gprod * (vec_a[i] + i * alpha + beta) ) % curve_order

    A1 = crs_h[0]
    for i in range(1,n):
        A1 = add(A1, crs_h[i])
    A1 = multiply(A1, beta)
    A1 = add(A1, multiply(M, alpha))
    A1 = add(A1, A)

    start = timer()
    [current_hash, inner_prod_info] = gprod_verify(current_hash, crs[:], A1, len(ciphertexts_R), gprod,
    gprod_proof[:],n,logn)
    end = timer()
    gprod_time =  end - start
    [vec_crs_h_exp, C, inner_prod, len_gprod] = inner_prod_info[:]

    start = timer()
    R = compute_multiexp(ciphertexts_R[:], vec_a[:])
    S = compute_multiexp(ciphertexts_S[:], vec_a[:])
    end = timer()

    R_S_time = end - start

    (current_hash, b) = sameexp_verify(current_hash, R, S, T, U, sameexp_proof[:])

    if b != 1:
        print("VERIFICATION FAILURE: does not have same exponent")
        return 0

    while len(ciphertexts_T) < n:
        ciphertexts_T.append(Z1)
        ciphertexts_U.append(Z1)


    start = timer()
    [current_hash, b] = verify_multiexp_and_gprod_inner(current_hash, crs[:], vec_crs_h_exp, len_gprod, C, inner_prod,
      ciphertexts_T[:], ciphertexts_U[:], A, T, U, inner_proof[:],n, logn)
    end = timer()

    print("hash_time = ", hash_time)
    print("R_S_time = ", R_S_time)
    print("gprod_time = ", gprod_time)
    print("inner product time = ", end - start)

    if b != 1:
        print("VERIFICATION FAILURE: does not have correct inner product")
        return 0

    return 1
