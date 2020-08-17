from group_ops import add, multiply, Z1, G1
from random import randint
from utils import curve_order

##### Totally insecure setup.  Just a placeholder.  Replace before usage.
def get_crs(n):
    crs = [0]*n


    for i in range(n):
        a = randint(1,curve_order-1)
        crs[i] = multiply(G1, a)

    return crs

##### Generation of example ciphertexts.  For testing.
def get_ciphertexts(n):
    ciphertexts_R = [0]*n
    ciphertexts_S = [0]*n

    for i in range(n):
        r = randint(1,curve_order-1)
        s = randint(1,curve_order-1)
        ciphertexts_R[i] = multiply(G1, r)
        ciphertexts_S[i] = multiply(G1, s)

    return [ciphertexts_R, ciphertexts_S]
