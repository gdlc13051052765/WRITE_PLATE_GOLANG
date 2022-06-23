#!/bin/sh

insmod /lib/modules/4.1.15+/kernel/drivers/net/wireless/bcmdhd/bcmdhd.ko
usleep 500000
wpa_supplicant -Dnl80211 -iwlan0 -c/etc/wpa_supplicant.conf -B > /dev/null 2>&1
sleep  2
udhcpc -b -i wlan0
