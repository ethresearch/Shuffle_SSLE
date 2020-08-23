from group_ops import add, multiply, Z1
from fiat_shamir import hash_integers
from utils import curve_order
from secrets import randbelow

def sameexp_prove(current_hash, g1, g2, h1, h2, y1, y2, exp, bl1, bl2):

    r = randbelow(curve_order)
    s = randbelow(curve_order)
    t = randbelow(curve_order)
    R1 = add(multiply(g1, r), multiply(h1, s));
    R2 = add(multiply(g2, r), multiply(h2, t));

    current_hash = hash_integers([current_hash, int(g1[0]), int(g1[1]), int(g1[2]),
    int(g2[0]), int(g2[1]), int(g2[2]),int(y1[0]), int(y1[1]), int(y1[2]),
    int(y2[0]), int(y2[1]), int(y2[2]), int(R1[0]), int(R1[1]), int(R1[2]),
    int(R2[0]), int(R2[1]), int(R2[2])])

    x = current_hash % curve_order

    u1 = (r + x * exp) % curve_order
    u2 = (s + x * bl1) % curve_order
    u3 = (t + x * bl2) % curve_order

    return (current_hash, [R1, R2, u1, u2, u3])

def sameexp_verify(current_hash, g1, g2, h1, h2, y1, y2, sameexp_proof):

    [R1, R2,u1, u2, u3] = sameexp_proof[:]

    current_hash = hash_integers([current_hash, int(g1[0]), int(g1[1]), int(g1[2]),
    int(g2[0]), int(g2[1]), int(g2[2]),int(y1[0]), int(y1[1]), int(y1[2]),
    int(y2[0]), int(y2[1]), int(y2[2]), int(R1[0]), int(R1[1]), int(R1[2]),
    int(R2[0]), int(R2[1]), int(R2[2])])

    x = current_hash % curve_order

    outcome1 = add(R1, multiply(y1, x))
    outcome1 = add(outcome1, multiply(g1, curve_order - u1))
    outcome1 = add(outcome1, multiply(h1, curve_order - u2))

    outcome2 = add(R2, multiply(y2, x))
    outcome2 = add(outcome2, multiply(g2, curve_order - u1))
    outcome2 = add(outcome2, multiply(h2, curve_order - u3))

    if outcome1 != Z1:
        print("ERROR: schnorr proof doesn't verify Z1")
        return (current_hash, 0)

    if outcome2 != Z1:
        print("ERROR: schnorr proof doesn't verify Z2")
        return (current_hash, 0)

    return (current_hash, 1)
