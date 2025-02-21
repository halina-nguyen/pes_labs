#include <zephyr/kernel.h>
#include <stdio.h>
#include <zephyr/device.h>
#include <zephyr/devicetree.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/sensor.h>


int main(void) {
    const struct device *bme680 = DEVICE_DT_GET_ANY(bosch_bme680);

    if (bme680 == NULL) {
        printf("No device found; did initialization fail?\n");
        return -1;
    } 
    
    struct sensor_value temp;

    while (1) {
        if (sensor_sample_fetch(bme680) < 0) {
            printf("ERROR: Sensor fetch failed\n");
            exit(0);
        }

        if (sensor_channel_get(bme680, SENSOR_CHAN_AMBIENT_TEMP, &temp) < 0) {
            printf("ERROR: Coudn't read sensor data\n");
            exit(0);
        }

        printf("Temperature: %.2f°C\n", sensor_value_to_double(&temp));
        k_sleep(K_SECONDS(3));
    }

    return 0;
}
