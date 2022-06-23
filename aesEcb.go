package main

import (
	"crypto/aes"
	"encoding/hex"
	"errors"
	"fmt"
)

func AESEncrypt(src []byte, key []byte) (encrypted []byte) {
	cipher, _ := aes.NewCipher(generateecbKey(key))
	length := (len(src) + aes.BlockSize) / aes.BlockSize
	plain := make([]byte, length*aes.BlockSize)
	copy(plain, src)
	pad := byte(len(plain) - len(src))
	for i := len(src); i < len(plain); i++ {
		plain[i] = pad
	}
	encrypted = make([]byte, len(plain))

	for bs, be := 0, cipher.BlockSize(); bs <= len(src); bs, be = bs+cipher.BlockSize(), be+cipher.BlockSize() {
		cipher.Encrypt(encrypted[bs:be], plain[bs:be])
	}

	return encrypted
}

func AESDecrypt(encrypted []byte, key []byte) (decrypted []byte, err error) {
	cipher, _ := aes.NewCipher(generateecbKey(key))
	decrypted = make([]byte, len(encrypted))
	for bs, be := 0, cipher.BlockSize(); bs < len(encrypted); bs, be = bs+cipher.BlockSize(), be+cipher.BlockSize() {
		if be < bs {
			err = errors.New("decrypted length error")
			return decrypted[0:0], err
		}
		if be > len(decrypted) || be > len(encrypted) {
			err = errors.New("decrypted length error")
			return decrypted[0:0], err
		}
		cipher.Decrypt(decrypted[bs:be], encrypted[bs:be])
	}

	trim := 0
	if len(decrypted) < 1 {
		err = errors.New("len decrypted length error")
		return decrypted[0:0], err
	}
	if len(decrypted) < int(decrypted[len(decrypted)-1]) {
		err = errors.New("decrypted length error")
		return decrypted[0:0], err
	} else {
		trim = len(decrypted) - int(decrypted[len(decrypted)-1])
	}

	err = nil
	return decrypted[:trim], err
}

func generateecbKey(key []byte) (genKey []byte) {
	genKey = make([]byte, 16)
	copy(genKey, key)
	for i := 16; i < len(key); {
		for j := 0; j < 16 && i < len(key); j, i = j+1, i+1 {
			genKey[j] ^= key[i]
		}
	}
	return genKey
}

func TestAESDecrypt() {
	expected := "SSIDSSIDSSIDSSIDSSIDSSIDSSIDSSIDSSIDSSID"
	encrypted := AESEncrypt([]byte("SSIDSSIDSSIDSSIDSSIDSSIDSSIDSSIDSSIDSSID"), []byte("rlnqflkewnlfwnjf"))
	fmt.Printf("encrypted = %x \n", encrypted)
	decrypted, _ := AESDecrypt(encrypted, []byte("rlnqflkewnlfwnjf"))
	if string(decrypted) != expected {
		fmt.Printf("AESDecrypt mismatch(%x:%x)", string(decrypted), expected)
	}
	fmt.Printf("AESDecrypt = %s ; %x\n", string(decrypted), expected)

	expected = "日本語文字列"
	encrypted, _ = hex.DecodeString("e5dc9002f2f09d88b85356d93ee9f1f9fdde4874face19e7cda4af28a796a38a")
	decrypted1, _ := AESDecrypt(encrypted, []byte("testcryptkey"))
	if string(decrypted1) != expected {
		fmt.Printf("AESDecrypt(Japanese character) mismatch(%x:%x)", string(decrypted1), expected)
	}

	expected = ""
	encrypted, _ = hex.DecodeString("59A597C079C4A25CB8BA415A74204020")
	decrypted2, _ := AESDecrypt(encrypted, []byte("testcryptkey"))
	if string(decrypted2) != expected {
		fmt.Printf("AESDecrypt(empty value) mismatch(%x:%x)", string(decrypted2), expected)
	}
}
