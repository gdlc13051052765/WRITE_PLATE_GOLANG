echo 8 > /sys/class/gpio/export
echo out > /sys/class/gpio/gpio8/direction
echo 0 > /sys/class/gpio/gpio8/value