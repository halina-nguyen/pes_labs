#include <zephyr/kernel.h>
#include <zephyr/device.h>
#include <zephyr/devicetree.h>
#include <zephyr/drivers/gpio.h>
#include <zephyr/drivers/i2c.h>
#include <stdio.h>
#include <bme680_reg.h>

#define BME680_ADDR     0x77
#define I2C_LABEL       i2c0


int main(void) {
    const struct device *i2c_bus = DEVICE_DT_GET(DT_NODELABEL(I2C_LABEL));

    if (i2c_bus == NULL) {
        printf("No device found; did initialization fail?\n");
        return -1;
    } 
    
    // try and read chip id
    uint8_t id;
    if (i2c_reg_read_byte(i2c_bus, BME680_ADDR, BME680_ID, &id) < 0){
        printf("Could not communicate with sensor.\n"); 
        return -1; 
    }
    
    if (id != 0x61) {
        printf("Sensor ID could not be read from I2C device.\n");
        return -1;
    }

    while (1) {
        uint8_t temp_raw[3];

        // start temperature measurement
        i2c_reg_write_byte(i2c_bus, BME680_ADDR, BME680_CTRL_MEAS, 0x25);
        k_sleep(K_MSEC(100));

        // read raw temperature data
        if (i2c_burst_read(i2c_bus, BME680_ADDR, BME680_TEMP_MSB, temp_raw, 3) < 0) {
            printf("ERROR: Couldn't read temperature data\n");
            exit(0);
        }

        // convert raw to temperature values
        int32_t adc_temp = ((temp_raw[0] << 16) | (temp_raw[1] << 8) | temp_raw[2]) >> 4;
        float temperature = ((float)adc_temp / 100.0f);

        printf("Temperature: %.2f°C\n", temperature);
        k_sleep(K_SECONDS(3));
    }

    return 0;
}
