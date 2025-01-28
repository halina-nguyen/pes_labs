#include "pico/stdlib.h"
/* !!! PART 2 & 3 !!! */
#include "pico/util/queue.h"
#include "hardware/pwm.h"
/* !!! MIGHT WANT TO CHANGE THIS !!! */
#define BUTTON_DEBOUNCE_DELAY   50
#define EVENT_QUEUE_SIZE 10

static uint32_t last_interrupt_time_b1 = 0;
static uint32_t last_interrupt_time_b2 = 0;

const uint b1_PIN20 = 20;
const uint b2_PIN21 = 21;
const uint b3_PIN22 = 22;
const uint LED_PIN0 = 0 ;
const uint LED_PIN1 = 1 ;
const uint LED_PIN2 = 2 ;
const uint LED_PIN3 = 3 ;
/* Function pointer primitive */ 
typedef void (*state_func_t)( void );

typedef struct _state_t
{
    uint8_t id;
    state_func_t Enter;
    state_func_t Do;
    state_func_t Exit;
    uint32_t delay_ms;
} state_t;

typedef enum _event_t 
{
    b1_evt = 0,
    b2_evt = 1,
    b3_evt = 2,
    no_evt = 3
} event_t;

/* !!! PART 2 & 3 !!! */
/* Define event queue */
queue_t event_queue;

void button_isr(uint gpio, uint32_t events) 
{
    uint32_t current_time = to_ms_since_boot(get_absolute_time());

    if (gpio == b1_PIN20) {
        if (current_time - last_interrupt_time_b1 > BUTTON_DEBOUNCE_DELAY) {
            event_t evt = b1_evt;
            queue_try_add(&event_queue, &evt);
        }
        last_interrupt_time_b1 = current_time;
    }

    if (gpio == b2_PIN21) {
        if (current_time - last_interrupt_time_b2 > BUTTON_DEBOUNCE_DELAY) {
            event_t evt = b2_evt;
            queue_try_add(&event_queue, &evt);
        }
        last_interrupt_time_b2 = current_time;
    }

    if (gpio == b3_PIN22) {  // Handle button 3
        static uint32_t last_interrupt_time_b3 = 0;
        if (current_time - last_interrupt_time_b3 > BUTTON_DEBOUNCE_DELAY) {
            event_t evt = b3_evt;
            queue_try_add(&event_queue, &evt);
        }
        last_interrupt_time_b3 = current_time;
    }
}



void private_init() 
{
    /* !!! PART 2 !!! */
    /* Event queue setup */ 
queue_init(&event_queue, sizeof(event_t), EVENT_QUEUE_SIZE);

    /* !!! PART 2 !!! */
    /* Button setup */

gpio_init(b1_PIN20);
gpio_init(b2_PIN21);
gpio_init(b3_PIN22);
gpio_set_dir(b1_PIN20, GPIO_IN);
gpio_set_dir(b2_PIN21, GPIO_IN);
gpio_set_dir(b3_PIN22, GPIO_IN);        
gpio_pull_up(b1_PIN20);
gpio_pull_up(b2_PIN21);
gpio_pull_up(b3_PIN22);   

gpio_set_irq_enabled_with_callback(b3_PIN22, GPIO_IRQ_EDGE_FALL, true, &button_isr);
gpio_set_irq_enabled_with_callback(b1_PIN20, GPIO_IRQ_EDGE_FALL, true, &button_isr);
gpio_set_irq_enabled_with_callback(b2_PIN21, GPIO_IRQ_EDGE_FALL, true, &button_isr);

    /* !!! PART 1 !!! */
    /* LED setup */


gpio_init(LED_PIN0);
gpio_init(LED_PIN1);
gpio_init(LED_PIN2);
gpio_init(LED_PIN3);
gpio_set_dir(LED_PIN0, GPIO_OUT);
gpio_set_dir(LED_PIN1, GPIO_OUT);
gpio_set_dir(LED_PIN2, GPIO_OUT);
gpio_set_dir(LED_PIN3, GPIO_OUT);
 

}

/* The next three methods are for convenience, you might want to use them. */
event_t get_event(void)
{
    /* !!!! PART 2 !!!! */
    event_t evt;
    if (queue_try_remove(&event_queue, &evt)) 
    {
        return evt;
    }
    return (event_t) no_evt;
}

void leds_off () 
{
    /* !!! PART 1 !!! */
    gpio_put(LED_PIN0, 0);
    gpio_put(LED_PIN1, 0);
    gpio_put(LED_PIN2, 0);
    gpio_put(LED_PIN3, 0);
}

void leds_on () 
{
    /* !!! PART 2 !!! */
    gpio_put(LED_PIN0, 1);
    gpio_put(LED_PIN1, 1);
    gpio_put(LED_PIN2, 1);
    gpio_put(LED_PIN3, 1);
}

void pwm_init_led(uint pin) {
    gpio_set_function(pin, GPIO_FUNC_PWM);
    uint slice_num = pwm_gpio_to_slice_num(pin);
    pwm_config config = pwm_get_default_config();
    pwm_config_set_clkdiv(&config, 64.0f);
    pwm_init(slice_num, &config, true);
    pwm_set_gpio_level(pin, 0);
}


void fade_led(uint pin) {
    uint slice_num = pwm_gpio_to_slice_num(pin);
    for (int i = 0; i <= 255; i++) {
        pwm_set_gpio_level(pin, i * i);
        sleep_ms(10);
    }
    for (int i = 255; i >= 0; i--) {
        pwm_set_gpio_level(pin, i * i);
        sleep_ms(10);
    }
}



void do_state_0(void)
{
    /* !!! PART 1 !!! */

  for (int i = 0; i <= 3; i++)
   {  
    gpio_put(i, 1);
    sleep_ms(500);
    gpio_put(i, 0);
   }
}

void do_state_1(void)
{
    /* !!! PART 2 !!! */

  
    
    leds_on () ;
    sleep_ms(500);
    leds_off () ;;
   
}


void do_state_2(void)
{
    /* !!! PART 2 !!! */

  for (int i = 3; i >= 0; i--)
   {  
    gpio_put(i, 1);
    sleep_ms(300);
    gpio_put(i, 0);
   }
}


void do_state_3(void)
{
    /* !!! PART 3 !!! */

  fade_led(LED_PIN0);
}

void enter_state_3(void) {
    pwm_init_led(LED_PIN0);  // Initialize PWM for LED_PIN0
}

void exit_state_3(void) {
    pwm_set_gpio_level(LED_PIN0, 0);          // Turn off the LED
    gpio_set_function(LED_PIN0, GPIO_FUNC_SIO);  // Reset GPIO pin to default
    gpio_set_dir(LED_PIN0, GPIO_OUT);
}

/* !!! PART 1 !!! */
const state_t state0 = {
    0, 
    NULL,
    do_state_0,
    NULL, 
    500
};

const state_t state1 = {
    1, 
    NULL,
    do_state_1,
    NULL, 
    500
};


const state_t state2 = {
    2, 
    NULL,
    do_state_2,
    NULL, 
    500
};

const state_t state3 = {
    3, 
    enter_state_3,
    do_state_3,
    exit_state_3, 
    0
};

/* !!! PART 2 !!! */
// const state_t state_table[][] = {};
const state_t* state_table[4][4] = 
{  
    { &state2,  &state1, &state3, &state0 },  
    { &state0,  &state2, &state3, &state1 },  
    { &state1,  &state0, &state3, &state2 },
    { &state0,  &state0, &state0, &state3 }   
};


/* !!! ALL PARTS !!! */
int main() 
{
    private_init(); 

    const state_t* current_state = &state0;
    event_t evt = no_evt;
    
    for(;;) 
    {
        if (current_state->Enter)
        {
          current_state->Enter();  
        };
        evt = get_event();

        while(evt == no_evt)

        {
            current_state->Do();
            sleep_ms(current_state->delay_ms);
            evt = get_event();
        } 
        
        if (current_state->Exit)
        {
          current_state->Exit();  
        };

        current_state = state_table[current_state->id][evt];


    }
}

