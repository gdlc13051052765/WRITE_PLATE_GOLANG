kill -9 $(pidof golang)
sleep 1
kill -9 $(pidof WriteDisk)
sleep 1
/home/meican/writeDiskAppBakup/WriteDisk &
sleep 1
/home/meican/writeDiskAppBakup/golang &
