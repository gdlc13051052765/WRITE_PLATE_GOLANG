ifconfig wlan0 down
kill -9 $(pidof  wpa_supplicant)
ifconfig wlan0 up
/opt/mc_shell/wifi_connect.sh

