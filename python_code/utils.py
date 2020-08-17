from py_ecc.optimized_bn128 import Z1
from py_ecc.fields import optimized_bn128_FQ as FQ

from group_ops import add, multiply
import ctypes
from ctypes import *
cdll.LoadLibrary("libff.dylib")
lib = CDLL("libff.dylib")

curve_order = 21888242871839275222246405745257275088548364400416034343698204186575808495617

def compute_innerprod(a,b):
    outcome = 0
    for i in range(len(a)):
        outcome = ( outcome + a[i] * b[i] ) % curve_order

    return outcome

def arr_to_ctypes_arr(arr):
    ctypes_arr = (ctypes.c_char_p * len(arr))()
    ctypes_arr[:] = list(map(lambda x: int(x).to_bytes(32, 'little'), arr))
    return ctypes_arr

def compute_multiexp_2(a,b):

    outcome = multiply(a[0], b[0])
    if len(a)==0:
        return outcome

    for i in range(1,len(a)):
        outcome = add(outcome, multiply(a[i], b[i]))

    return outcome

def compute_multiexp(crs, vec):
    if vec == []:
        return Z1

    crs_subset = crs[:len(vec)]
    exponents = arr_to_ctypes_arr([vec[i] for i in range(len(vec))])
    points_x = arr_to_ctypes_arr(list(map(lambda p: int(p[0]), crs_subset)))
    points_y = arr_to_ctypes_arr(list(map(lambda p: int(p[1]), crs_subset)))
    points_z = arr_to_ctypes_arr(list(map(lambda p: int(p[2]), crs_subset)))

    res_x = ctypes.c_buffer(32)
    res_y = ctypes.c_buffer(32)
    res_z = ctypes.c_buffer(32)
    lib.multiexp(exponents, len(exponents), points_x, points_y, points_z, len(crs_subset), res_x, res_y, res_z);
    F = (int.from_bytes(res_x, byteorder='little', signed=False), int.from_bytes(res_y, byteorder='little', signed=False), int.from_bytes(res_z, byteorder='little', signed=False))

#    return (FQ(F[0]),FQ(F[1]),FQ(F[2]))
    return F


def inverse(a):
    if a == 0:
        print("ERROR: No inverse exists")
        return "ERROR"

    a = a % curve_order;

    t1 = 0;
    t2 = 1;
    r1 = curve_order;
    r2 = a;

    while (r2 != 0):
        q = r1 // r2 ;
        t1old = t1; r1old = r1;

        t1 = t2;
        t2 = t1old - q * t2
        r1 = r2
        r2 = r1old - q * r2

    if (t1 < 0):
        return (curve_order + t1);
    return t1;

def int_to_binaryintarray(x,logn):
    y = bin(x)[2:]
    z = [0] * (logn)
    for i in range(len(y)):
        z[i] = int(y[len(y) - i - 1])
    return z
