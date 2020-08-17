import hashlib
from eth_abi import encode_abi
from py_ecc.secp256k1.secp256k1 import bytes_to_int

def hash_integers(values):
    k = bytes(32)

    for i in range(0,len(values)):
        k1 = int(values[i]).to_bytes(32, byteorder='big')
        v = encode_abi(['bytes32','bytes32'],[k,k1])
        k = hashlib.sha256(v).digest()

    return bytes_to_int(k)

#print("hash_integers",hash_integers([2,3,4]))
