# PGP-ECC

PGP-ECC Crypto Module – A core cryptosystem implementing Pretty Good Privacy (PGP) with Elliptic Curve Cryptography (ECC) for secure end-to-end encrypted communication. Developed in Python, it supports key generation, encryption/decryption, and digital signatures.


## note
note : everything build it from scratch !!!


## features
-  **ECC Key Generation** — Generates elliptic curve key pairs for asymmetric cryptography.  
-  **PGP-Style Encryption & Decryption** — Hybrid encryption combining ECC (for key exchange) and symmetric ciphers (for message confidentiality).  
-  **Digital Signatures** — Signs and verifies messages for integrity and authenticity.  
-  **Secure Key Exchange** — Implements ECC-based ephemeral key agreement for session encryption.  
-  **Modular Design** — Core crypto components (keys, encryption, signatures) implemented in separate modules for extensibility.



## Tech Stack
- **Language:** Python  
- **Core Concepts:** ECC, PGP, Hybrid Encryption, Digital Signatures, Key Management, NIST P-256  
- **Implemented From Scratch:**  
  - Finite field arithmetic  
  - Elliptic curve point operations  
  - Keypair and signature generation  
  - PGP-like packet structure for message encryption



