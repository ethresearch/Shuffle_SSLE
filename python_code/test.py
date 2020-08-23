from group_ops import add, multiply, Z1
from timeit import default_timer as timer

from setup import get_crs, get_ciphertexts

from prove import shuffle, shuffle_prove, shuffle_verify
from utils import compute_multiexp, curve_order
from random import randint



crs = get_crs(131)
crs = [crs[:128],crs[128],crs[129],crs[130]]

num_ciphertexts = 124
num_blinders = 4

[ciphertexts_R, ciphertexts_S] = get_ciphertexts(num_ciphertexts)

print("start shuffle")
start = timer()
(ciphertexts_T, ciphertexts_U, shuffle, r) = shuffle(ciphertexts_R[:], ciphertexts_S[:])
end = timer()
print("end shuffle", end - start)

print("start prover")
start = timer()
shuffle_proof = shuffle_prove(crs[:], num_blinders, ciphertexts_R[:], ciphertexts_S[:],
ciphertexts_T[:], ciphertexts_U[:], shuffle[:], r)
end = timer()
prover_time = end - start
print("end prover", end - start)

print("start verifier")
start = timer()
b = shuffle_verify(crs[:], num_blinders, ciphertexts_R[:], ciphertexts_S[:],
ciphertexts_T[:], ciphertexts_U[:], shuffle_proof[:])
end = timer()
verifier_time = end - start
print("end verifier", end - start)

print("prover_time =", prover_time, "verifier_time =", verifier_time)

print("b = ", b)
