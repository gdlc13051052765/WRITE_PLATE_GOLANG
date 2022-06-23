#!/bin/sh

/opt/mc_shell/wifi_connect.sh &
sleep 5

/home/meican/setblue.sh &
sleep 1

/home/meican/WriteDisk &

sleep 1

/home/meican/golang &

sleep 1

/home/meican/writeplateProcessProtrction &

#/opt/mc_shell/wifi_connect.sh &

