#!/bin/sh
# set bitrate
echo Setting up CAN0 bitrate to 1000000.
ip link set can0 type can bitrate 1000000 restart-ms 1000

# bring CAN0 up
ip link set can0 up
echo CAN0 is ready.
