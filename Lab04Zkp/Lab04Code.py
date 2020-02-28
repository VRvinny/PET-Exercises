#####################################################
# GA17 Privacy Enhancing Technologies -- Lab 04
#
# Zero Knowledge Proofs
#
# Run the tests through:
# $ py.test -v test_file_name.py

###########################
# Group Members: TODO
###########################

from petlib.ec import EcGroup
from petlib.bn import Bn

from hashlib import sha256
from binascii import hexlify

def setup():
    """ Generates the Cryptosystem Parameters. """
    G = EcGroup(nid=713)
    g = G.hash_to_point(b"g")
    hs = [G.hash_to_point(("h%s" % i).encode("utf8")) for i in range(4)]
    o = G.order()
    return (G, g, hs, o)

def keyGen(params):
   """ Generate a private / public key pair. """
   (G, g, hs, o) = params
   priv = o.random()
   pub = priv * g
   return (priv, pub)

def to_challenge(elements):
    """ Generates a Bn challenge by hashing a number of EC points """
    Cstring = b",".join([hexlify(x.export()) for x in elements])
    Chash =  sha256(Cstring).digest()
    return Bn.from_binary(Chash)

#####################################################
# TASK 1 -- Prove knowledge of a DH public key's 
#           secret.

def proveKey(params, priv, pub):
    """ Uses the Schnorr non-interactive protocols produce a proof 
        of knowledge of the secret priv such that pub = priv * g.

        Outputs: a proof (c, r)
                 c (a challenge)
                 r (the response)
    """  
    (G, g, hs, o) = params
    
    
    # W = g^w Witness
    # pub = g^x
    # priv = x
    
    # witness
    w = o.random()
    W = w * g 
    
    #challenge
    c = to_challenge([g, W])
    
    # send r = w - cx
    r = (w - (c * priv)) % o
        
    return (c, r)

def verifyKey(params, pub, proof):
    """ Schnorr non-interactive proof verification of knowledge of a a secret.
        Returns a boolean indicating whether the verification was successful.
    """
    (G, g, hs, o) = params
    c, r = proof
    # g^ gw_prime == W == g^w
    gw_prime  = c * pub + r * g 
    return to_challenge([g, gw_prime]) == c

#####################################################
# TASK 2 -- Prove knowledge of a Discrete Log 
#           representation.

def commit(params, secrets):
    """ Produces a commitment C = r * g + Sum xi * hi, 
        where secrets is a list of xi of length 4.
        Returns the commitment (C) and the opening (r).
    """
    assert len(secrets) == 4
    (G, g, (h0, h1, h2, h3), o) = params
    x0, x1, x2, x3 = secrets
    r = o.random()
    C = x0 * h0 + x1 * h1 + x2 * h2 + x3 * h3 + r * g
    return (C, r)

def proveCommitment(params, C, r, secrets):
    """ Prove knowledge of the secrets within a commitment, 
        as well as the opening of the commitment.

        Args: C (the commitment), r (the opening of the 
                commitment), and secrets (a list of secrets).
        Returns: a challenge (c) and a list of responses.
    """
    (G, g, (h0, h1, h2, h3), o) = params
    x0, x1, x2, x3 = secrets

    # generate the witnesses
    
    w1 = o.random()
    w2 = o.random()
    w3 = o.random()
    w4 = o.random()
    w5 = o.random()
    
    #
    W1 = w1 * g
    W2 = w2 * h0
    W3 = w3 * h1
    W4 = w4 * h2
    W5 = w5 * h3
    
    W = W1 + W2 + W3 + W4 + W5
    
    c = to_challenge([g, h0, h1, h2, h3, W ])
    
    # r = (w - (c * priv)) % o
    # generate the responses
    rr = (w1 - (c * r)) % o
    r0 = (w2 - (c * x0)) % o
    r1 = (w3 - (c * x1)) % o
    r2 = (w4 - (c * x2)) % o
    r3 = (w5 - (c * x3)) % o

    responses = (r0, r1, r2, r3, rr)
    
    return (c, responses)

def verifyCommitments(params, C, proof):
    """ Verify a proof of knowledge of the commitment.
        Return a boolean denoting whether the verification succeeded. """
    (G, g, (h0, h1, h2, h3), o) = params
    c, responses = proof
    (r0, r1, r2, r3, rr) = responses

    # C^c * h0^r0 *  h1^r1 * h2^r2 * h3^r3 * g^rr
    Cw_prime = c * C + r0 * h0 + r1 * h1 + r2 * h2 + r3 * h3 + rr * g
    c_prime = to_challenge([g, h0, h1, h2, h3, Cw_prime])
    return c_prime == c

#####################################################
# TASK 3 -- Prove Equality of discrete logarithms.
#

def gen2Keys(params):
    """ Generate two related public keys K = x * g and L = x * h0. """
    (G, g, (h0, h1, h2, h3), o) = params
    x = o.random()

    K = x * g
    L = x * h0

    return (x, K, L)    

def proveDLEquality(params, x, K, L):
    """ Generate a ZK proof that two public keys K, L have the same secret private key x, 
        as well as knowledge of this private key. """
    (G, g, (h0, h1, h2, h3), o) = params
    
    
    # K, L are public keys
    # K = g^ x      |  L= h^x = h0^x
    
    #w for witness
    w = o.random()
    Kw = w * g
    Lw = w * h0

    c = to_challenge([g, h0, Kw, Lw])

    r = (w - c * x) % o
    return (c, r)

def verifyDLEquality(params, K, L, proof):
    """ Return whether the verification of equality of two discrete logarithms succeeded. """ 
    (G, g, (h0, h1, h2, h3), o) = params
    c, r = proof
    
    # repeat what happens in task1
    gw_prime = c * K + r * g 
    hw_prime = c * L + r * h0
    
    return to_challenge([g, h0, gw_prime, hw_prime]) == c

#####################################################
# TASK 4 -- Prove correct encryption and knowledge of 
#           a plaintext.

def encrypt(params, pub, m):
    """ Encrypt a message m under a public key pub. 
        Returns both the randomness and the ciphertext.
    """
    (G, g, (h0, h1, h2, h3), o) = params
    k = o.random()
    return k, (k * g, k * pub + m * h0)

def proveEnc(params, pub, Ciphertext, k, m):
    """ Prove in ZK that the ciphertext is well formed 
        and knowledge of the message encrypted as well.

        Return the proof: challenge and the responses.
    """ 
    (G, g, (h0, h1, h2, h3), o) = params
    a, b = Ciphertext

    ## YOUR CODE HERE:

    w0 = o.random()
    w1 = o.random()

    
    # rm = w0 - c*k
    
    wKey = w0 * g
    wMessage = w1 * g 
    # wMessage = 

    c = to_challenge([g, h0, h1, wKey])

    rk = w0 - c*k % o
    
    rm = w1 - c*m % o

    return (c, (rk, rm))

def verifyEnc(params, pub, Ciphertext, proof):
    """ Verify the proof of correct encryption and knowledge of a ciphertext. """
    (G, g, (h0, h1, h2, h3), o) = params
    a, b = Ciphertext    
    (c, (rk, rm)) = proof

    # (a,b) = (k*g, k*pub + m*h0)
    # (a,b) = (k*g, k*x*g + m*h0)

    # proof of knowledge of key and correct a

    #g^rk * g^ck = g^w0
    # cipher text is given meaning 
    #g^rk * a^c = g^w0
    #  
    #rk*g + c*a = w0*g

    responseKey = rk*g + c*a

    # want g^w1
    # g^w1 = g^rm *g^c^m

    
    # responseMessage = rm*g + 


    c = to_challenge([g, h0, h1, responseKey])




    return ## YOUR RETURN HERE


#####################################################
# TASK 5 -- Prove a linear relation
#

def relation(params, x1):
    """ Returns a commitment C to x0 and x1, such that x0 = 10 x1 + 20,
        as well as x0, x1 and the commitment opening r. 
    """
    (G, g, (h0, h1, h2, h3), o) = params
    r = o.random()

    x0 = (10 * x1 + 20)
    C = r * g + x1 * h1 + x0 * h0

    return C, x0, x1, r

def prove_x0eq10x1plus20(params, C, x0, x1, r):
    """ Prove C is a commitment to x0 and x1 and that x0 = 10 x1 + 20. """
    (G, g, (h0, h1, h2, h3), o) = params

    '''
	normally would do 
	gen w1, w2 
	calc W = g^w1 h ^w2
	c = H(g,h,C, W)
	r1 = w1 - Cv
	r2 = w2 - Co

	send (c,r1,r2)

	but with the existence of a relation we can do

	W = g^w1* h1^w2 * h2^(10w2)



    '''
    w1 = o.random()
    w2 = o.random()

    W = w1*g + w2*h1 + 10*w2*h0

    c = to_challenge([g, h0, h1, W])


    r1 = w1 - c*r %o
    r2 = w2 - c*x1 %o

    return (c, r1, r2) 

def verify_x0eq10x1plus20(params, C, proof):
    """ Verify that proof of knowledge of C and x0 = 10 x1 + 20. """
    (G, g, (h0, h1, h2, h3), o) = params

    '''
    modify H(g,h,C, g^r1 h^r2 C^c)

    to 

    H(g,h0,h1,)
    H(g,h0,h1, (C * h0^-20)^c)
    H(g,h0,h1, g^r1 * h1^r2 * h1^10r2 * (h0^-20 *C )^c )


    #C = r * g + x1 * h1 + x0 * h0

    # want W = w1*g + w2*h1 + 10*w2*h0 
    converted to elliptic curves this becomes

    '''
    (c, r1, r2) = proof
    
    calcWit = r1*g + r2*h1 + r2*10*h0 + c*(-20*h0  + C)

    calcChal = to_challenge([g,h0,h1,calcWit])

    return c == calcChal

#####################################################
# TASK 6 -- (OPTIONAL) Prove that a ciphertext is either 0 or 1


def binencrypt(params, pub, m):
    """ Encrypt a binary value m under public key pub """
    assert m in [0, 1]
    (G, g, (h0, h1, h2, h3), o) = params
    
    k = o.random()
    return k, (k * g, k * pub + m * h0)

def provebin(params, pub, Ciphertext, k, m):
    """ Prove a ciphertext is valid and encrypts a binary value either 0 or 1. """
    pass

def verifybin(params, pub, Ciphertext, proof):
    """ verify that proof that a cphertext is a binary value 0 or 1. """
    pass

def test_bin_correct():
    """ Test that a correct proof verifies """
    pass

def test_bin_incorrect():
    """ Prove that incorrect proofs fail. """
    pass
#####################################################
# TASK Q1 - Answer the following question:
#
# The interactive Schnorr protocol (See PETs Slide 8) offers 
# "plausible deniability" when performed with an 
# honest verifier. The transcript of the 3 step interactive 
# protocol could be simulated without knowledge of the secret 
# (see Slide 12). Therefore the verifier cannot use it to prove 
# to a third party that the holder of secret took part in the 
# protocol acting as the prover.
#
# Does "plausible deniability" hold against a dishonest verifier 
# that  deviates from the Schnorr identification protocol? Justify 
# your answer by describing what a dishonest verifier may do.

""" TODO: Your answer here. """

#####################################################
# TASK Q2 - Answer the following question:
#
# Consider the function "prove_something" below, that 
# implements a zero-knowledge proof on commitments KX
# and KY to x and y respectively. Note that the prover
# only knows secret y. What statement is a verifier, 
# given the output of this function, convinced of?
#
# Hint: Look at "test_prove_something" too.

""" TODO: Your answer here. """

def prove_something(params, KX, KY, y):
    (G, g, _, o) = params

    # Simulate proof for KX
    # r = wx - cx => g^w = g^r * KX^c 
    rx = o.random()
    c1 = o.random()
    W_KX = rx * g + c1 * KX

    # Build proof for KY
    wy = o.random()
    W_KY = wy * g
    c = to_challenge([g, KX, KY, W_KX, W_KY])

    # Build so that: c1 + c2 = c (mod o)
    c2 = (c - c1) % o
    ry = ( wy - c2 * y ) % o

    # return proof
    return (c1, c2, rx, ry)

import pytest

def test_prove_something():
    params = setup()
    (G, g, hs, o) = params

    # Commit to x and y
    x = o.random()
    y = o.random()
    KX = x*g
    KY = y*g

    # Pass only y
    (c1, c2, rx, ry) = prove_something(params, KX, KY, y)

    # Verify the proof
    W_KX = rx * g + c1 * KX
    W_KY = ry * g + c2 * KY
    c = to_challenge([g, KX, KY, W_KX, W_KY])
    assert c % o == (c1 + c2) % o

