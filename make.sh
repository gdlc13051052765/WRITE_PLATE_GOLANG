rm -rf golang
CGO_ENABLED=1 GOOS=linux GOARCH=arm GOARM=5 CC=arm-linux-gnueabihf-gcc go build
rm -rf otafiles/ota/golang
rm -rf otafiles/ota/version.txt
cp golang otafiles/ota
cp version.txt otafiles/ota
#scp -r golang root@192.168.3.81:/home/meican
