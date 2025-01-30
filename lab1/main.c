#include "pico/stdlib.h"
#include "pico/util/queue.h"
#include "hardware/pwm.h"

#define BUTTON_DEBOUNCE_DELAY  50
#define EVENT_QUEUE_SIZE       10
#define BRIGHTNESS_STEP        10

// buttons pins
const uint b1 = 20;
const uint b2 = 21;
const uint b3 = 22;

// LED pins
const uint led0 = 0 ;
const uint led1 = 1 ;
const uint led2 = 2 ;
const uint led3 = 3 ;

typedef void (*state_func_t)(void);

// structure of state
typedef struct _state_t {
    uint8_t id;
    state_func_t Enter;
    state_func_t Do;
    state_func_t Exit;
    uint32_t delay_ms;
} state_t;

// events
typedef enum _event_t {
    b1_evt = 0,
    b2_evt = 1,
    b3_evt = 2,
    no_evt = 3
} event_t;

queue_t event_queue;

// handle events by pressing button
void button_isr(uint gpio, uint32_t events) {
    // consider button debouncing
    if ((to_ms_since_boot(get_absolute_time()) - button_time) > BUTTON_DEBOUNCE_DELAY) {
        button_time = to_ms_since_boot(get_absolute_time());

        switch (gpio) {
            case b1:
                event_t evt = b1_evt;
                break; 
            case b2:
                event_t evt = b2_evt;
                break;
            case b3:
                event_t evt = b3_evt;
                break;
            default:
                return;
        }
        queue_try_add(&event_queue, &evt);
    }
}

void private_init() {
    // event queue setup
    queue_init(&event_queue, sizeof(event_t), EVENT_QUEUE_SIZE);

    // button setup
    gpio_init(b1);
    gpio_set_dir(b1, GPIO_IN);
    gpio_pull_up(b1);
    gpio_set_irq_enabled_with_callback(b1, GPIO_IRQ_EDGE_FALL, true, &button_isr);

    gpio_init(b2);
    gpio_set_dir(b2, GPIO_IN);
    gpio_pull_up(b2);
    gpio_set_irq_enabled_with_callback(b2, GPIO_IRQ_EDGE_FALL, true, &button_isr);

    gpio_init(b3);
    gpio_set_dir(b3, GPIO_IN);
    gpio_pull_up(b3);
    gpio_set_irq_enabled_with_callback(b3, GPIO_IRQ_EDGE_FALL, true, &button_isr);

    // LED setup
    gpio_init(led0);
    gpio_set_dir(led0, GPIO_OUT);

    gpio_init(led1);
    gpio_set_dir(led1, GPIO_OUT);

    gpio_init(led2);
    gpio_set_dir(led2, GPIO_OUT);

    gpio_init(led3);
    gpio_set_dir(led3, GPIO_OUT);
}

// read event from queue
event_t get_event(void) {
    event_t evt;
    if (queue_try_remove(&event_queue, &evt)) return evt;
    return (event_t) no_evt;
}

// turn LEDs off
void leds_off() {
    gpio_put(led0, 0);
    gpio_put(led1, 0);
    gpio_put(led2, 0);
    gpio_put(led3, 0);
}

// turn LEDs on
void leds_on() {
    gpio_put(led0, 1);
    gpio_put(led1, 1);
    gpio_put(led2, 1);
    gpio_put(led3, 1);
}

void pwm_init_led(uint pin) {
    gpio_set_function(pin, GPIO_FUNC_PWM);
    uint slice_num = pwm_gpio_to_slice_num(pin);
    //pwm_config config = pwm_get_default_config();
    //pwm_config_set_clkdiv(&config, 64.0f);
    //pwm_init(slice_num, &config, true);
    pwm_set_wrap(slice_num, 255);
    pwm_set_gpio_level(pin, 0);
    pwm_set_enabled(slice_num, 1);
}

// state functions
void enter_state(void) {
    leds_off();
}

void exit_state(void) {
    leds_off();
}

void do_state_0(void) {
    static uint current_led = 0;

    leds_off();
    gpio_put(LED[current_led], 1);
    current_led = (current_led + 1) % 4;
}

void do_state_1(void) {
    static bool on = false;

    if (on) leds_off();
    else leds_on();

    on = !on;
}

void do_state_2(void) {
    static int8_t current_led = 3;

    leds_off();
    gpio_put(current_led, 1);
    current_led = (current_led - 1) % 4;
}

void enter_state_3(void) {
    leds_off();

    pwm_init_led(led0);
}

void exit_state_3(void) {
    pwm_set_gpio_level(led0, 0);
    gpio_set_function(led0, GPIO_FUNC_SIO);
    gpio_set_dir(led0, GPIO_OUT);

    leds_off();
}

void do_state_3(void) {
    static uint bright = 0;
    static bool incr = true;

    pwm_set_gpio_level(led0, bright);

    if (incr) {
        bright += BRIGHTNESS_STEP;
        if (bright >= 255) incr = false;
    } else {
        bright -= BRIGHTNESS_STEP;
        if (bright <= 0) incr = true;
    }
}

// states
const state_t state0 = {0, enter_state,   do_state_0, exit_state,   500};
const state_t state1 = {1, enter_state,   do_state_1, exit_state,   500};
const state_t state2 = {2, enter_state,   do_state_2, exit_state,   250};
const state_t state3 = {3, enter_state_3, do_state_3, exit_state_3,  20};

// state transition
const state_t* state_table[4][4] = {
    {&state2, &state1, &state3, &state0},
    {&state0, &state2, &state3, &state1},
    {&state1, &state0, &state3, &state2},
    {&state0, &state0, &state0, &state3}
};

int main() {
    private_init(); 

    state_t* current_state = &state0;
    event_t evt = no_evt;

    current_state.Enter();
    evt = get_event();

    while(1) {
        current_state->Do();
        sleep_ms(current_state->delay_ms);
        evt = get_event();

        if (evt != no_evt) {
            current_state.Exit();
            current_state = state_table[current_state.id][evt];
            current_state.Enter();
        }
    }
}